/* Copyright (C) 2024 John Törnblom

This program is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation; either version 3, or (at your option) any
later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; see the file COPYING. If not, see
<http://www.gnu.org/licenses/>.  */

/*
 * meme_dumper - PS5 Kernel Memory Dumper
 *
 * Ported to ps5-payload-dev SDK for etaHEN compatibility.
 *
 * This tool provides kernel memory dumping functionality via TCP connection.
 * It uses the DMAP (Direct Map Area) technique to access physical memory.
 *
 * Commands:
 *   kinfo       - Display kernel information (bases, pmap, DMAP)
 *   dump_base   - Dump 1MB from kernel .data base
 *   dump_vaddr <addr> <size> - Dump memory from virtual address
 *   dump_paddr <addr> <size> - Dump memory from physical address via DMAP
 *   dump_pte <vaddr>         - Walk page tables for virtual address
 *   scan_pte <va> <n> [s]    - Scan PTEs for address range
 *   cmp_sections             - Compare .text vs .data page mappings
 *   probe_xom                - Analyze XOM protection mechanism
 *   dump_idt                 - Dump IDT (handlers, IST, types)
 *   find_doreti_iret         - Find doreti_iret gadget in kernel .text
 *   exit        - Close connection
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <unistd.h>
#include <errno.h>
#include <signal.h>
#include <setjmp.h>
#include <stdint.h>

#include <sys/socket.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <threads.h>
#include <ucontext.h>
#include <sys/cpuset.h>
#include <pthread.h>
#include <pthread_np.h>

#include <ps5/kernel.h>

/* x86 CPU intrinsics for CPUID */
static inline void
do_cpuid(unsigned int ax, unsigned int *p)
{
    __asm__ __volatile__ ("cpuid"
        : "=a" (p[0]), "=b" (p[1]), "=c" (p[2]), "=d" (p[3])
        : "0" (ax), "c" (0));
}

/* APIC base address */
#define DEFAULT_APIC_BASE       0xfee00000

/* Signal handling for fault-safe probing */
static sigjmp_buf probe_jmp_env;
static volatile sig_atomic_t probe_fault_occurred;

/* Step 7: #GP trap frame method state */
static volatile sig_atomic_t gp_trap_stop_writer;
static volatile sig_atomic_t gp_trap_got_result;
static volatile uint64_t     gp_trap_doreti_addr;
static volatile uint64_t     gp_trap_mc_cs;
static volatile uint64_t     gp_trap_mc_err;
static sigjmp_buf            gp_trap_jmp_env;
static volatile sig_atomic_t gp_trap_attempt_count;
static volatile int          gp_trap_sig_received;

/* Server configuration */
#define SERVER_PORT 9023
#define BUFFER_SIZE 4096
#define DUMP_CHUNK_SIZE 0x4000

/* FreeBSD pmap structure offsets (PS5 specific) */
#define PMAP_OFFSET_PM_PML4    0x00
#define PMAP_OFFSET_PM_CR3     0x08
/* DMAP base is calculated dynamically: dmap_base = pmap[0x20] - pmap[0x28] */
#define PMAP_OFFSET_DMAP_VADDR 0x20   /* Contains a DMAP virtual address */
#define PMAP_OFFSET_DMAP_PADDR 0x28   /* Contains corresponding physical address */

/* pmap_store offset from kernel data base - FW 4.03 */
#define PMAP_STORE_OFFSET      0x3257a78

/* Kernel CR3 (KPML4phys) - 8 bytes before pmap_store */
#define KERNEL_CR3_OFFSET      0x3257a70

/* x86-64 Page Table Constants */
#define PAGE_SHIFT_4K       12
#define PAGE_SIZE_4K        (1UL << PAGE_SHIFT_4K)
#define PAGE_MASK_4K        (PAGE_SIZE_4K - 1)

#define PDRSHIFT            21      /* 2MB page */
#define PDPSHIFT            30      /* 1GB page */
#define PML4SHIFT           39

/* Page sizes for large pages */
#ifndef NBPDR
#define NBPDR               (1UL << PDRSHIFT)   /* 2MB */
#endif
#ifndef NBPDP
#define NBPDP               (1UL << PDPSHIFT)   /* 1GB */
#endif

/* Page table entry flags */
#define PTE_P               0x001   /* Present */
#define PTE_RW              0x002   /* Read/Write */
#define PTE_US              0x004   /* User/Supervisor */
#define PTE_PWT             0x008   /* Write-Through */
#define PTE_PCD             0x010   /* Cache Disable */
#define PTE_A               0x020   /* Accessed */
#define PTE_D               0x040   /* Dirty */
#define PTE_PS              0x080   /* Page Size (2MB or 1GB) */
#define PTE_G               0x100   /* Global */
#define PTE_NX              (1UL << 63)  /* No Execute */

/* Physical address masks */
#define PTE_FRAME           0x000FFFFFFFFFF000UL  /* 4KB page frame */
#define PDE_PS_FRAME        0x000FFFFFFFE00000UL  /* 2MB page frame */
#define PDPE_PS_FRAME       0x000FFFFFC0000000UL  /* 1GB page frame */

/* Extract page table indices from virtual address */
#define PML4_INDEX(va)      (((va) >> PML4SHIFT) & 0x1FF)
#define PDP_INDEX(va)       (((va) >> PDPSHIFT) & 0x1FF)
#define PD_INDEX(va)        (((va) >> PDRSHIFT) & 0x1FF)
#define PT_INDEX(va)        (((va) >> PAGE_SHIFT_4K) & 0x1FF)

/* Notification support */
typedef struct notify_request {
    char useless1[45];
    char message[3075];
} notify_request_t;

int sceKernelSendNotificationRequest(int, notify_request_t*, size_t, int);

static void
notify(const char *msg) {
    notify_request_t req;
    bzero(&req, sizeof(req));
    strncpy(req.message, msg, sizeof(req.message) - 1);
    sceKernelSendNotificationRequest(0, &req, sizeof(req), 0);
}

/*
 * Calculate DMAP base dynamically from pmap_store.
 * DMAP base = (DMAP vaddr at offset 0x20) - (phys addr at offset 0x28)
 */
static uint64_t
get_dmap_base(void) {
    intptr_t kdata_base = KERNEL_ADDRESS_DATA_BASE;
    intptr_t pmap_store = kdata_base + PMAP_STORE_OFFSET;

    uint64_t dmap_vaddr = kernel_getlong(pmap_store + PMAP_OFFSET_DMAP_VADDR);
    uint64_t dmap_paddr = kernel_getlong(pmap_store + PMAP_OFFSET_DMAP_PADDR);

    return dmap_vaddr - dmap_paddr;
}

/*
 * Get the kernel's CR3 (physical address of kernel PML4).
 * This is stored at KERNEL_CR3_OFFSET, NOT in pmap_store.
 */
static uint64_t
get_kernel_cr3(void) {
    intptr_t kdata_base = KERNEL_ADDRESS_DATA_BASE;
    return kernel_getlong(kdata_base + KERNEL_CR3_OFFSET);
}

/* Send formatted response to client */
static void
send_response(int sock, const char *fmt, ...) {
    char buf[BUFFER_SIZE];
    va_list args;

    va_start(args, fmt);
    vsnprintf(buf, sizeof(buf), fmt, args);
    va_end(args);

    send(sock, buf, strlen(buf), 0);
}

/* Read kernel memory and send to client */
static int
dump_memory(int sock, intptr_t addr, size_t size) {
    uint8_t *buf;
    size_t remaining = size;
    size_t offset = 0;
    int ret = 0;

    buf = malloc(DUMP_CHUNK_SIZE);
    if (!buf) {
        send_response(sock, "ERROR: malloc failed\n");
        return -1;
    }

    send_response(sock, "DUMP_START:%zu\n", size);

    while (remaining > 0) {
        size_t chunk = (remaining > DUMP_CHUNK_SIZE) ? DUMP_CHUNK_SIZE : remaining;

        if (kernel_copyout(addr + offset, buf, chunk) != 0) {
            send_response(sock, "\nERROR: kernel_copyout failed at offset 0x%zx\n", offset);
            ret = -1;
            break;
        }

        ssize_t sent = send(sock, buf, chunk, 0);
        if (sent != (ssize_t)chunk) {
            ret = -1;
            break;
        }

        offset += chunk;
        remaining -= chunk;
    }

    free(buf);
    send_response(sock, "\nDUMP_END\n");
    return ret;
}

/*
 * Walk page tables to translate virtual address to physical address (verbose)
 * Returns 0 on success, -1 on failure
 */
static int
vaddr_to_paddr(int sock, uint64_t vaddr, uint64_t dmap_base, uint64_t pm_cr3,
               uint64_t *paddr_out, uint64_t *pte_flags_out)
{
    uint64_t pml4e, pdpe, pde, pte;
    uint64_t pml4_paddr, pdp_paddr, pd_paddr, pt_paddr;
    uint64_t pml4_idx, pdp_idx, pd_idx, pt_idx;
    uint64_t page_offset;

    /* Extract indices from virtual address */
    pml4_idx = PML4_INDEX(vaddr);
    pdp_idx = PDP_INDEX(vaddr);
    pd_idx = PD_INDEX(vaddr);
    pt_idx = PT_INDEX(vaddr);

    send_response(sock, "  VA: 0x%lx -> indices: PML4[%lu] PDP[%lu] PD[%lu] PT[%lu]\n",
                  vaddr, pml4_idx, pdp_idx, pd_idx, pt_idx);

    /* Step 1: Read PML4 entry */
    pml4_paddr = (pm_cr3 & PTE_FRAME) + (pml4_idx * 8);
    pml4e = kernel_getlong(dmap_base + pml4_paddr);

    send_response(sock, "  PML4E[%lu] @ paddr 0x%lx = 0x%lx\n",
                  pml4_idx, pml4_paddr, pml4e);

    if (!(pml4e & PTE_P)) {
        send_response(sock, "  ERROR: PML4E not present\n");
        return -1;
    }

    /* Step 2: Read PDP entry */
    pdp_paddr = (pml4e & PTE_FRAME) + (pdp_idx * 8);
    pdpe = kernel_getlong(dmap_base + pdp_paddr);

    send_response(sock, "  PDPE[%lu] @ paddr 0x%lx = 0x%lx\n",
                  pdp_idx, pdp_paddr, pdpe);

    if (!(pdpe & PTE_P)) {
        send_response(sock, "  ERROR: PDPE not present\n");
        return -1;
    }

    /* Check for 1GB huge page */
    if (pdpe & PTE_PS) {
        page_offset = vaddr & (NBPDP - 1);
        *paddr_out = (pdpe & PDPE_PS_FRAME) + page_offset;
        if (pte_flags_out) *pte_flags_out = pdpe;
        send_response(sock, "  1GB page: paddr = 0x%lx (flags=0x%lx)\n",
                      *paddr_out, pdpe & 0xFFF);
        return 0;
    }

    /* Step 3: Read PD entry */
    pd_paddr = (pdpe & PTE_FRAME) + (pd_idx * 8);
    pde = kernel_getlong(dmap_base + pd_paddr);

    send_response(sock, "  PDE[%lu] @ paddr 0x%lx = 0x%lx\n",
                  pd_idx, pd_paddr, pde);

    if (!(pde & PTE_P)) {
        send_response(sock, "  ERROR: PDE not present\n");
        return -1;
    }

    /* Check for 2MB huge page */
    if (pde & PTE_PS) {
        page_offset = vaddr & (NBPDR - 1);
        *paddr_out = (pde & PDE_PS_FRAME) + page_offset;
        if (pte_flags_out) *pte_flags_out = pde;
        send_response(sock, "  2MB page: paddr = 0x%lx (flags=0x%lx)\n",
                      *paddr_out, pde & 0xFFF);
        return 0;
    }

    /* Step 4: Read PT entry (4KB page) */
    pt_paddr = (pde & PTE_FRAME) + (pt_idx * 8);
    pte = kernel_getlong(dmap_base + pt_paddr);

    send_response(sock, "  PTE[%lu] @ paddr 0x%lx = 0x%lx\n",
                  pt_idx, pt_paddr, pte);

    if (!(pte & PTE_P)) {
        send_response(sock, "  ERROR: PTE not present\n");
        return -1;
    }

    page_offset = vaddr & PAGE_MASK_4K;
    *paddr_out = (pte & PTE_FRAME) + page_offset;
    if (pte_flags_out) *pte_flags_out = pte;

    send_response(sock, "  4KB page: paddr = 0x%lx (flags=0x%lx)\n",
                  *paddr_out, pte & 0xFFF);
    return 0;
}

/*
 * Walk page tables quietly (no output) for scanning
 */
static int
vaddr_to_paddr_quiet(uint64_t dmap_base, uint64_t pm_cr3, uint64_t vaddr,
                     uint64_t *paddr_out, uint64_t *pte_flags_out)
{
    uint64_t pml4e, pdpe, pde, pte;
    uint64_t page_offset;

    /* PML4 */
    pml4e = kernel_getlong(dmap_base + (pm_cr3 & PTE_FRAME) + (PML4_INDEX(vaddr) * 8));
    if (!(pml4e & PTE_P)) return -1;

    /* PDP */
    pdpe = kernel_getlong(dmap_base + (pml4e & PTE_FRAME) + (PDP_INDEX(vaddr) * 8));
    if (!(pdpe & PTE_P)) return -1;

    if (pdpe & PTE_PS) {
        page_offset = vaddr & (NBPDP - 1);
        *paddr_out = (pdpe & PDPE_PS_FRAME) + page_offset;
        if (pte_flags_out) *pte_flags_out = pdpe;
        return 0;
    }

    /* PD */
    pde = kernel_getlong(dmap_base + (pdpe & PTE_FRAME) + (PD_INDEX(vaddr) * 8));
    if (!(pde & PTE_P)) return -1;

    if (pde & PTE_PS) {
        page_offset = vaddr & (NBPDR - 1);
        *paddr_out = (pde & PDE_PS_FRAME) + page_offset;
        if (pte_flags_out) *pte_flags_out = pde;
        return 0;
    }

    /* PT */
    pte = kernel_getlong(dmap_base + (pde & PTE_FRAME) + (PT_INDEX(vaddr) * 8));
    if (!(pte & PTE_P)) return -1;

    page_offset = vaddr & PAGE_MASK_4K;
    *paddr_out = (pte & PTE_FRAME) + page_offset;
    if (pte_flags_out) *pte_flags_out = pte;
    return 0;
}

/*
 * dump_pte - Walk page tables for a virtual address
 * Usage: dump_pte <vaddr>
 */
static void
cmd_dump_pte(int sock, const char *args)
{
    unsigned long vaddr;
    uint64_t paddr, pte_flags;

    if (sscanf(args, "%lx", &vaddr) != 1) {
        send_response(sock, "ERROR: Usage: dump_pte <vaddr>\n");
        return;
    }

    uint64_t pm_cr3 = get_kernel_cr3();
    uint64_t dmap_base = get_dmap_base();

    send_response(sock, "=== Page Table Walk for VA 0x%lx ===\n", vaddr);
    send_response(sock, "Kernel CR3: 0x%lx, DMAP: 0x%lx\n\n", pm_cr3, dmap_base);

    if (vaddr_to_paddr(sock, vaddr, dmap_base, pm_cr3, &paddr, &pte_flags) == 0) {
        send_response(sock, "\n=== Translation Result ===\n");
        send_response(sock, "VA 0x%lx -> PA 0x%lx\n", vaddr, paddr);
        send_response(sock, "Flags: P=%d RW=%d US=%d PWT=%d PCD=%d A=%d D=%d PS=%d G=%d NX=%d\n",
                      !!(pte_flags & PTE_P),
                      !!(pte_flags & PTE_RW),
                      !!(pte_flags & PTE_US),
                      !!(pte_flags & PTE_PWT),
                      !!(pte_flags & PTE_PCD),
                      !!(pte_flags & PTE_A),
                      !!(pte_flags & PTE_D),
                      !!(pte_flags & PTE_PS),
                      !!(pte_flags & PTE_G),
                      !!(pte_flags & PTE_NX));

        /* Check if this is execute-only (NX=0, RW=0) */
        if (!(pte_flags & PTE_NX) && !(pte_flags & PTE_RW)) {
            send_response(sock, "WARNING: This page appears to be EXECUTE-ONLY (XOM)\n");
        }
    }
    send_response(sock, "OK\n");
}

/*
 * scan_pte - Scan page table entries for a range
 * Usage: scan_pte <start_vaddr> <count> [stride]
 */
static void
cmd_scan_pte(int sock, const char *args)
{
    unsigned long start_vaddr, count, stride = 0x1000;
    uint64_t paddr, pte_flags;

    int parsed = sscanf(args, "%lx %lx %lx", &start_vaddr, &count, &stride);
    if (parsed < 2) {
        send_response(sock, "ERROR: Usage: scan_pte <start_vaddr> <count> [stride]\n");
        return;
    }
    if (stride == 0) stride = 0x1000;
    if (count > 256) count = 256;

    uint64_t pm_cr3 = get_kernel_cr3();
    uint64_t dmap_base = get_dmap_base();

    send_response(sock, "=== PTE Scan: 0x%lx + %lu entries (stride 0x%lx) ===\n",
                  start_vaddr, count, stride);
    send_response(sock, "%-18s %-18s %-6s %-4s %-4s %-5s\n",
                  "VADDR", "PADDR", "FLAGS", "RW", "NX", "XOM");
    send_response(sock, "--------------------------------------------------------------\n");

    for (unsigned long i = 0; i < count; i++) {
        uint64_t va = start_vaddr + (i * stride);

        if (vaddr_to_paddr_quiet(dmap_base, pm_cr3, va, &paddr, &pte_flags) == 0) {
            int is_xom = (!(pte_flags & PTE_NX) && !(pte_flags & PTE_RW));
            send_response(sock, "0x%016lx 0x%016lx 0x%04lx %-4s %-4s %-5s\n",
                          va, paddr, pte_flags & 0xFFF,
                          (pte_flags & PTE_RW) ? "RW" : "RO",
                          (pte_flags & PTE_NX) ? "NX" : "X",
                          is_xom ? "YES" : "");
        } else {
            send_response(sock, "0x%016lx UNMAPPED\n", va);
        }
    }
    send_response(sock, "OK\n");
}

/*
 * cmp_sections - Compare .text vs .data page table mappings
 */
static void
cmd_cmp_sections(int sock)
{
    intptr_t ktext_base = KERNEL_ADDRESS_TEXT_BASE;
    intptr_t kdata_base = KERNEL_ADDRESS_DATA_BASE;
    uint64_t text_paddr = 0, text_flags = 0;
    uint64_t data_paddr = 0, data_flags = 0;

    uint64_t pm_cr3 = get_kernel_cr3();
    uint64_t dmap_base = get_dmap_base();

    send_response(sock, "=== Kernel Section Comparison ===\n\n");

    /* Analyze kernel .text */
    send_response(sock, "--- Kernel .text (0x%lx) ---\n", ktext_base);
    if (vaddr_to_paddr(sock, ktext_base, dmap_base, pm_cr3, &text_paddr, &text_flags) == 0) {
        send_response(sock, "Physical: 0x%lx\n", text_paddr);
        send_response(sock, "Flags: RW=%d NX=%d (XOM=%s)\n",
                      !!(text_flags & PTE_RW),
                      !!(text_flags & PTE_NX),
                      (!(text_flags & PTE_NX) && !(text_flags & PTE_RW)) ? "YES" : "NO");
    }

    send_response(sock, "\n--- Kernel .data (0x%lx) ---\n", kdata_base);
    if (vaddr_to_paddr(sock, kdata_base, dmap_base, pm_cr3, &data_paddr, &data_flags) == 0) {
        send_response(sock, "Physical: 0x%lx\n", data_paddr);
        send_response(sock, "Flags: RW=%d NX=%d\n",
                      !!(data_flags & PTE_RW),
                      !!(data_flags & PTE_NX));
    }

    /* Calculate offsets */
    send_response(sock, "\n=== Analysis ===\n");
    send_response(sock, "Text-Data VA offset: 0x%lx\n", kdata_base - ktext_base);
    if (text_paddr && data_paddr) {
        send_response(sock, "Text-Data PA offset: 0x%lx\n",
                      (data_paddr > text_paddr) ? data_paddr - text_paddr : text_paddr - data_paddr);
    }
    send_response(sock, "OK\n");
}

/*
 * probe_xom - Diagnose XOM enforcement level (SAFE - no reads from .text)
 *
 * WARNING: Previous version caused kernel panic by attempting to read
 * from kernel .text. The PS5 hypervisor enforces XOM and crashes on
 * any attempt to read code pages.
 *
 * This version only analyzes page table flags without reading protected memory.
 */
static void
cmd_probe_xom(int sock)
{
    intptr_t ktext_base = KERNEL_ADDRESS_TEXT_BASE;
    intptr_t kdata_base = KERNEL_ADDRESS_DATA_BASE;
    uint64_t text_paddr = 0, text_flags = 0;
    uint64_t data_paddr = 0, data_flags = 0;

    uint64_t pm_cr3 = get_kernel_cr3();
    uint64_t dmap_base = get_dmap_base();

    send_response(sock, "=== XOM Probe Analysis (SAFE MODE) ===\n\n");
    send_response(sock, "WARNING: Reading kernel .text causes kernel panic!\n");
    send_response(sock, "This indicates HV-enforced XOM protection.\n\n");

    /* Analyze kernel .text page table entry */
    send_response(sock, "=== Kernel .text (0x%lx) ===\n", ktext_base);
    if (vaddr_to_paddr(sock, ktext_base, dmap_base, pm_cr3, &text_paddr, &text_flags) == 0) {
        send_response(sock, "\nPhysical address: 0x%lx\n", text_paddr);
        send_response(sock, "Page flags: 0x%lx\n", text_flags & 0x8000000000000FFFUL);
        send_response(sock, "  Present:  %d\n", !!(text_flags & PTE_P));
        send_response(sock, "  RW:       %d (0=Read-Only)\n", !!(text_flags & PTE_RW));
        send_response(sock, "  User:     %d\n", !!(text_flags & PTE_US));
        send_response(sock, "  Accessed: %d\n", !!(text_flags & PTE_A));
        send_response(sock, "  NX:       %d (0=Executable)\n", !!(text_flags & PTE_NX));

        int is_xom = (!(text_flags & PTE_NX) && !(text_flags & PTE_RW));
        send_response(sock, "  XOM:      %s\n", is_xom ? "YES (Execute-Only)" : "NO");
    }

    /* Analyze kernel .data page table entry for comparison */
    send_response(sock, "\n=== Kernel .data (0x%lx) ===\n", kdata_base);
    if (vaddr_to_paddr(sock, kdata_base, dmap_base, pm_cr3, &data_paddr, &data_flags) == 0) {
        send_response(sock, "\nPhysical address: 0x%lx\n", data_paddr);
        send_response(sock, "Page flags: 0x%lx\n", data_flags & 0x8000000000000FFFUL);
        send_response(sock, "  Present:  %d\n", !!(data_flags & PTE_P));
        send_response(sock, "  RW:       %d\n", !!(data_flags & PTE_RW));
        send_response(sock, "  User:     %d\n", !!(data_flags & PTE_US));
        send_response(sock, "  Accessed: %d\n", !!(data_flags & PTE_A));
        send_response(sock, "  NX:       %d\n", !!(data_flags & PTE_NX));
    }

    /* Diagnosis */
    send_response(sock, "\n=== Diagnosis ===\n");
    if (text_paddr != 0) {
        int text_xom = (!(text_flags & PTE_NX) && !(text_flags & PTE_RW));
        if (text_xom) {
            send_response(sock, "Kernel .text has XOM page flags (NX=0, RW=0)\n");
            send_response(sock, "Combined with kernel panic on read attempt:\n");
            send_response(sock, "  -> XOM is HYPERVISOR-ENFORCED\n");
            send_response(sock, "  -> HV traps reads to code pages and crashes\n");
            send_response(sock, "  -> DMAP bypass does NOT work\n");
            send_response(sock, "\nTo dump kernel code, you would need:\n");
            send_response(sock, "  1. Hypervisor exploit (e.g., APIC timing attack)\n");
            send_response(sock, "  2. Or find unprotected code copy in memory\n");
        } else {
            send_response(sock, "Kernel .text does NOT have XOM page flags\n");
            send_response(sock, "But read attempt still caused panic - HV protection\n");
        }
    }

    send_response(sock, "OK\n");
}

/*
 * find_kcr3 - Search for the kernel's actual CR3/PML4
 * The pm_cr3 in pmap_store appears to be user-space CR3.
 * We search for a PML4 that has entry 511 present (kernel space mapping).
 */
static void
cmd_find_kcr3(int sock)
{
    uint64_t dmap_base = get_dmap_base();

    send_response(sock, "=== Searching for Kernel CR3 ===\n");
    send_response(sock, "DMAP base: 0x%lx\n\n", dmap_base);

    /* Strategy 1: Check some known physical addresses where kernel PML4 might be */
    uint64_t candidates[] = {
        0x1000000,   /* 16MB - common location */
        0x1001000,
        0x1002000,
        0x1010000,
        0x1020000,
        0x1030000,
        0x1040000,
        0x1100000,
        0x1200000,
        0x1400000,
        0x1430000,   /* Current pm_cr3 value */
        0x1500000,
        0x2000000,
        0x3000000,
        0x4000000,
    };

    send_response(sock, "Checking known physical addresses for valid kernel PML4...\n\n");

    for (int i = 0; i < (int)(sizeof(candidates) / sizeof(candidates[0])); i++) {
        uint64_t cr3_candidate = candidates[i];
        uint64_t pml4e_paddr = cr3_candidate + (511 * 8);  /* PML4E[511] */
        uint64_t pml4e = kernel_getlong(dmap_base + pml4e_paddr);

        /* Check if PML4E[511] is present and looks valid */
        int present = !!(pml4e & PTE_P);
        int rw = !!(pml4e & PTE_RW);
        uint64_t next_paddr = pml4e & PTE_FRAME;

        if (present && next_paddr != 0 && next_paddr < 0x800000000UL) {
            send_response(sock, "CANDIDATE CR3=0x%lx: PML4E[511]=0x%lx (P=%d RW=%d next=0x%lx)\n",
                          cr3_candidate, pml4e, present, rw, next_paddr);

            /* Verify by checking if PDP[511] is also present */
            uint64_t pdpe_paddr = next_paddr + (511 * 8);
            uint64_t pdpe = kernel_getlong(dmap_base + pdpe_paddr);
            int pdp_present = !!(pdpe & PTE_P);

            if (pdp_present) {
                send_response(sock, "  -> PDPE[511]=0x%lx (P=%d) - LIKELY VALID!\n",
                              pdpe, pdp_present);
            }
        }
    }

    /* Strategy 2: Try to find kernel CR3 from a global variable */
    send_response(sock, "\n=== Searching kernel globals for CR3 ===\n");

    intptr_t kdata_base = KERNEL_ADDRESS_DATA_BASE;

    /* Common offsets where KPML4phys might be stored */
    uint64_t global_offsets[] = {
        0x31dc4c8,  /* Possible KPML4phys offset */
        0x31dc4d0,
        0x31dc4d8,
        0x31dc500,
        0x31dc508,
        0x3257a70,
        0x3257a80,
    };

    for (int i = 0; i < (int)(sizeof(global_offsets) / sizeof(global_offsets[0])); i++) {
        uint64_t val = kernel_getlong(kdata_base + global_offsets[i]);

        /* Check if this looks like a valid CR3 (physical address, page-aligned) */
        if ((val & 0xFFF) == 0 && val > 0 && val < 0x800000000UL) {
            /* Try it as CR3 */
            uint64_t pml4e_paddr = val + (511 * 8);
            uint64_t pml4e = kernel_getlong(dmap_base + pml4e_paddr);

            if (pml4e & PTE_P) {
                send_response(sock, "FOUND at kdata+0x%lx: val=0x%lx -> PML4E[511]=0x%lx (PRESENT!)\n",
                              global_offsets[i], val, pml4e);
            }
        }
    }

    send_response(sock, "OK\n");
}

/*
 * dump_pmap - Dump raw pmap_store structure to find correct offsets
 */
static void
cmd_dump_pmap(int sock)
{
    intptr_t kdata_base = KERNEL_ADDRESS_DATA_BASE;
    intptr_t pmap_store = kdata_base + PMAP_STORE_OFFSET;

    send_response(sock, "=== Raw pmap_store dump ===\n");
    send_response(sock, "kdata_base:  0x%lx\n", kdata_base);
    send_response(sock, "pmap_store:  0x%lx (offset 0x%x)\n", pmap_store, PMAP_STORE_OFFSET);
    send_response(sock, "\nSearching for DMAP-like values (0xffff9...):\n\n");

    /* Dump first 0x400 bytes, showing non-zero and interesting values */
    for (int i = 0; i < 0x400; i += 8) {
        uint64_t val = kernel_getlong(pmap_store + i);

        /* Show if: non-zero, or looks like DMAP base (0xffff9...) or kernel ptr */
        if (val != 0) {
            const char *hint = "";
            if ((val >> 44) == 0xffff9) {
                hint = " <-- POSSIBLE DMAP BASE!";
            } else if ((val >> 32) == 0xffffffff) {
                hint = " (kernel ptr)";
            } else if ((val & 0xFFF) == 0 && val < 0x100000000UL && val != 0) {
                hint = " (possible phys addr)";
            }
            send_response(sock, "+0x%03x: 0x%016lx%s\n", i, val, hint);
        }
    }

    /* Also search for DMAP in nearby memory */
    send_response(sock, "\n=== Searching kernel globals for DMAP ===\n");
    /* Try some common offsets where DMAP might be stored */
    uint64_t test_offsets[] = {0x3257878, 0x3257a70, 0x3257a80, 0x3257b00, 0x3258000};
    for (int j = 0; j < 5; j++) {
        uint64_t val = kernel_getlong(kdata_base + test_offsets[j]);
        if ((val >> 44) == 0xffff9) {
            send_response(sock, "FOUND at kdata+0x%lx: 0x%016lx\n", test_offsets[j], val);
        }
    }

    send_response(sock, "OK\n");
}

/* =========================================================
 * HV BYPASS RESEARCH COMMANDS
 * ========================================================= */

/*
 * cpuid_info - Display CPU features relevant to HV bypass research
 * Usage: cpuid_info
 *
 * Uses CPUID to understand the virtualization environment and AMD-V/SVM features.
 * This is safe from userland and reveals HV configuration.
 */
static void
cmd_cpuid_info(int sock)
{
    unsigned int regs[4];
    char vendor[13] = {0};
    char hv_vendor[13] = {0};

    send_response(sock, "=== CPUID Analysis for HV Research ===\n\n");

    /* Basic CPUID - Vendor ID */
    do_cpuid(0, regs);
    memcpy(&vendor[0], &regs[1], 4);  /* EBX */
    memcpy(&vendor[4], &regs[3], 4);  /* EDX */
    memcpy(&vendor[8], &regs[2], 4);  /* ECX */
    send_response(sock, "CPU Vendor: %s\n", vendor);
    send_response(sock, "Max CPUID leaf: 0x%x\n\n", regs[0]);

    /* CPUID 1 - Feature flags */
    do_cpuid(1, regs);
    send_response(sock, "=== Feature Flags (CPUID.1) ===\n");
    send_response(sock, "ECX: 0x%08x  EDX: 0x%08x\n", regs[2], regs[3]);
    send_response(sock, "  VMX (Intel VT):     %s\n", (regs[2] & (1<<5)) ? "YES" : "NO");
    send_response(sock, "  x2APIC:             %s\n", (regs[2] & (1<<21)) ? "YES" : "NO");
    send_response(sock, "  Hypervisor present: %s\n", (regs[2] & (1<<31)) ? "YES" : "NO");

    /* Hypervisor detection - CPUID 0x40000000 */
    if (regs[2] & (1<<31)) {
        do_cpuid(0x40000000, regs);
        memcpy(&hv_vendor[0], &regs[1], 4);
        memcpy(&hv_vendor[4], &regs[2], 4);
        memcpy(&hv_vendor[8], &regs[3], 4);
        send_response(sock, "\n=== Hypervisor Info ===\n");
        send_response(sock, "HV Vendor ID: '%s'\n", hv_vendor);
        send_response(sock, "Max HV leaf: 0x%x\n", regs[0]);

        /* Try to get more HV info */
        if (regs[0] >= 0x40000001) {
            do_cpuid(0x40000001, regs);
            send_response(sock, "HV Interface: 0x%08x 0x%08x 0x%08x 0x%08x\n",
                          regs[0], regs[1], regs[2], regs[3]);
        }
    }

    /* AMD Extended Features - CPUID 0x80000001 */
    do_cpuid(0x80000001, regs);
    send_response(sock, "\n=== AMD Extended Features (0x80000001) ===\n");
    send_response(sock, "ECX: 0x%08x  EDX: 0x%08x\n", regs[2], regs[3]);
    send_response(sock, "  SVM (AMD-V):   %s\n", (regs[2] & (1<<2)) ? "YES" : "NO");
    send_response(sock, "  NX bit:        %s\n", (regs[3] & (1<<20)) ? "YES" : "NO");
    send_response(sock, "  1GB pages:     %s\n", (regs[3] & (1<<26)) ? "YES" : "NO");
    send_response(sock, "  RDTSCP:        %s\n", (regs[3] & (1<<27)) ? "YES" : "NO");

    /* AMD SVM Features - CPUID 0x8000000A */
    do_cpuid(0x8000000A, regs);
    send_response(sock, "\n=== AMD SVM Features (0x8000000A) ===\n");
    send_response(sock, "SVM Rev: %d, NASID: %d\n", regs[0] & 0xFF, regs[1]);
    send_response(sock, "EDX features: 0x%08x\n", regs[3]);
    send_response(sock, "  NPT (Nested Paging):    %s\n", (regs[3] & (1<<0)) ? "YES" : "NO");
    send_response(sock, "  LBR Virtualization:     %s\n", (regs[3] & (1<<1)) ? "YES" : "NO");
    send_response(sock, "  SVM Lock:               %s\n", (regs[3] & (1<<2)) ? "YES" : "NO");
    send_response(sock, "  NRIP Save:              %s\n", (regs[3] & (1<<3)) ? "YES" : "NO");
    send_response(sock, "  TSC Rate MSR:           %s\n", (regs[3] & (1<<4)) ? "YES" : "NO");
    send_response(sock, "  VMCB Clean:             %s\n", (regs[3] & (1<<5)) ? "YES" : "NO");
    send_response(sock, "  Flush by ASID:          %s\n", (regs[3] & (1<<6)) ? "YES" : "NO");
    send_response(sock, "  Decode Assists:         %s\n", (regs[3] & (1<<7)) ? "YES" : "NO");
    send_response(sock, "  Pause Filter:           %s\n", (regs[3] & (1<<10)) ? "YES" : "NO");
    send_response(sock, "  AVIC (AMD Virtual IC):  %s\n", (regs[3] & (1<<13)) ? "YES" : "NO");
    send_response(sock, "  V_VMSAVE_VMLOAD:        %s\n", (regs[3] & (1<<15)) ? "YES" : "NO");
    send_response(sock, "  VGIF:                   %s\n", (regs[3] & (1<<16)) ? "YES" : "NO");

    send_response(sock, "\n=== Implications for HV Bypass ===\n");
    send_response(sock, "If NPT=YES, XOM is likely enforced via nested page tables\n");
    send_response(sock, "AVIC virtualization may offer timing attack surface\n");
    send_response(sock, "OK\n");
}

/*
 * scan_rwx - Scan for RWX (writable+executable) pages
 * Usage: scan_rwx <start_vaddr> <end_vaddr> [stride]
 *
 * Scans page tables looking for pages where:
 *   - NX=0 (executable) AND RW=1 (writable) -> true RWX
 *   - These could be used to inject/execute code or contain unprotected copies
 */
static void
cmd_scan_rwx(int sock, const char *args)
{
    unsigned long start_va, end_va, stride = 0x200000; /* Default 2MB stride */
    uint64_t pm_cr3 = get_kernel_cr3();
    uint64_t dmap_base = get_dmap_base();
    int rwx_count = 0, exec_ro_count = 0, rw_nx_count = 0;
    int scanned = 0;

    if (sscanf(args, "%lx %lx %lx", &start_va, &end_va, &stride) < 2) {
        send_response(sock, "Usage: scan_rwx <start_vaddr> <end_vaddr> [stride]\n");
        send_response(sock, "Example: scan_rwx ffffffffc4800000 ffffffffc5000000 200000\n");
        return;
    }

    if (stride == 0) stride = 0x200000;
    if (end_va <= start_va) {
        send_response(sock, "ERROR: end_vaddr must be > start_vaddr\n");
        return;
    }

    send_response(sock, "=== RWX Page Scan: 0x%lx - 0x%lx ===\n", start_va, end_va);
    send_response(sock, "Stride: 0x%lx, CR3: 0x%lx, DMAP: 0x%lx\n\n", stride, pm_cr3, dmap_base);
    send_response(sock, "%-18s %-18s %-6s %-4s %-4s %-10s\n",
                  "VADDR", "PADDR", "FLAGS", "RW", "NX", "TYPE");
    send_response(sock, "--------------------------------------------------------------\n");

    for (uint64_t va = start_va; va < end_va && scanned < 4096; va += stride) {
        uint64_t paddr, flags;

        if (vaddr_to_paddr_quiet(dmap_base, pm_cr3, va, &paddr, &flags) == 0) {
            int is_exec = !(flags & PTE_NX);
            int is_write = !!(flags & PTE_RW);

            if (is_exec && is_write) {
                /* True RWX - highest interest */
                send_response(sock, "0x%016lx 0x%016lx 0x%04lx RW   X   **RWX**\n",
                              va, paddr, flags & 0xFFF);
                rwx_count++;
            } else if (is_exec && !is_write) {
                /* Execute-only or Read-Execute (potential XOM) */
                exec_ro_count++;
            } else if (!is_exec && is_write) {
                /* Normal data page (RW, NX) */
                rw_nx_count++;
            }
        }
        scanned++;
    }

    send_response(sock, "\n=== Summary ===\n");
    send_response(sock, "Pages scanned: %d\n", scanned);
    send_response(sock, "RWX pages (bypass candidates): %d\n", rwx_count);
    send_response(sock, "Exec+RO pages (XOM or code): %d\n", exec_ro_count);
    send_response(sock, "RW+NX pages (normal data): %d\n", rw_nx_count);

    if (rwx_count > 0) {
        send_response(sock, "\n*** FOUND RWX PAGES - POTENTIAL BYPASS VECTORS! ***\n");
    }
    send_response(sock, "OK\n");
}

/*
 * scan_code_sig - Search for kernel code signatures in accessible memory
 * Usage: scan_code_sig [start_paddr] [size]
 *
 * Searches DMAP-accessible memory for byte patterns that match
 * known kernel code sequences. May find unprotected copies of kernel code.
 */
static void
cmd_scan_code_sig(int sock, const char *args)
{
    unsigned long start_pa = 0x1000000;   /* Start at 16MB by default */
    unsigned long scan_size = 0x4000000;  /* 64MB default */
    uint64_t dmap_base = get_dmap_base();
    uint8_t buf[4096];
    int matches = 0;
    int chunks_read = 0;
    int chunks_failed = 0;

    /* Known kernel code signatures */
    /* swapgs; mov %rsp, %gs:xxx - syscall entry */
    static const uint8_t sig_swapgs[] = {0x0f, 0x01, 0xf8};
    /* iretq - interrupt return */
    static const uint8_t sig_iretq[] = {0x48, 0xcf};

    sscanf(args, "%lx %lx", &start_pa, &scan_size);

    /* Limit scan size to prevent excessive runtime */
    if (scan_size > 0x10000000) scan_size = 0x10000000;

    send_response(sock, "=== Code Signature Scan ===\n");
    send_response(sock, "Range: 0x%lx - 0x%lx (%lu MB)\n",
                  start_pa, start_pa + scan_size, scan_size / (1024*1024));
    send_response(sock, "DMAP base: 0x%lx\n", dmap_base);
    send_response(sock, "Searching for kernel code patterns...\n\n");

    for (uint64_t pa = start_pa; pa < start_pa + scan_size; pa += sizeof(buf)) {
        uint64_t va = dmap_base + pa;

        /* Try to read this chunk via kernel_copyout */
        if (kernel_copyout(va, buf, sizeof(buf)) != 0) {
            chunks_failed++;
            continue;
        }
        chunks_read++;

        /* Search for signatures in this chunk */
        for (size_t i = 0; i < sizeof(buf) - 16; i++) {
            /* Check swapgs signature (syscall entry) */
            if (memcmp(&buf[i], sig_swapgs, sizeof(sig_swapgs)) == 0) {
                send_response(sock, "MATCH: swapgs @ PA 0x%lx (DMAP 0x%lx)\n",
                              pa + i, va + i);
                matches++;
                if (matches > 100) goto done;  /* Limit output */
            }

            /* Check iretq (interrupt/syscall return) */
            if (memcmp(&buf[i], sig_iretq, sizeof(sig_iretq)) == 0) {
                /* Verify it's likely real code (check surrounding bytes) */
                if (i > 0 && (buf[i-1] == 0x48 || buf[i-1] == 0x41)) {
                    send_response(sock, "MATCH: iretq @ PA 0x%lx\n", pa + i);
                    matches++;
                    if (matches > 100) goto done;
                }
            }
        }
    }

done:
    send_response(sock, "\n=== Summary ===\n");
    send_response(sock, "Chunks read: %d, failed: %d\n", chunks_read, chunks_failed);
    send_response(sock, "Code signature matches: %d\n", matches);

    if (matches > 0 && chunks_failed == 0) {
        send_response(sock, "\n*** WARNING: Found code patterns in readable memory! ***\n");
        send_response(sock, "These may be unprotected copies of kernel code.\n");
    } else if (chunks_failed > chunks_read) {
        send_response(sock, "\nMost memory is not DMAP-accessible (HV protected)\n");
    }
    send_response(sock, "OK\n");
}

/*
 * msr_dump - Dump MSR values from kernel data structures
 * Usage: msr_dump
 *
 * Reads MSR values that the kernel has cached, since rdmsr
 * requires Ring 0 and would #GP from userland.
 */
static void
cmd_msr_dump(int sock)
{
    intptr_t kdata_base = KERNEL_ADDRESS_DATA_BASE;

    send_response(sock, "=== MSR Values from Kernel Structures ===\n\n");
    send_response(sock, "NOTE: Direct rdmsr requires Ring 0.\n");
    send_response(sock, "Scanning kernel .data for MSR-like values...\n\n");

    /* Look for EFER-like values: typical value is 0xD01 (LME|LMA|SCE|NXE) */
    send_response(sock, "=== Searching for EFER (0xC0000080) pattern ===\n");
    send_response(sock, "Expected: 0xD01 (LMA|LME|SCE) or 0xD00 | SVME\n\n");

    int efer_candidates = 0;
    for (uint64_t offset = 0; offset < 0x200000 && efer_candidates < 20; offset += 8) {
        uint64_t val = kernel_getlong(kdata_base + offset);

        /* EFER typical pattern: low bits set, upper bits zero */
        if ((val & 0xFFFFFFFFFFFF0000UL) == 0 &&
            (val & 0xD01) == 0xD01 &&           /* LMA, LME, SCE must be set */
            (val & 0xFFFFF000) == 0 &&          /* Upper bits clear */
            val != 0) {
            send_response(sock, "Possible EFER @ kdata+0x%lx: 0x%lx", offset, val);
            if (val & 0x1000) send_response(sock, " [SVME]");
            send_response(sock, "\n");
            efer_candidates++;
        }
    }

    /* Look for LSTAR (syscall entry point) - should be kernel address */
    send_response(sock, "\n=== Searching for LSTAR (0xC0000082) pattern ===\n");
    send_response(sock, "Expected: 0xffffffff8xxxxxxx (kernel .text address)\n\n");

    intptr_t ktext_base = KERNEL_ADDRESS_TEXT_BASE;
    int lstar_candidates = 0;
    for (uint64_t offset = 0; offset < 0x200000 && lstar_candidates < 10; offset += 8) {
        uint64_t val = kernel_getlong(kdata_base + offset);

        /* LSTAR should be in kernel .text range */
        if ((val >> 32) == 0xffffffff &&
            val >= (uint64_t)ktext_base &&
            val < (uint64_t)ktext_base + 0x2000000) {
            send_response(sock, "Possible LSTAR @ kdata+0x%lx: 0x%lx\n", offset, val);
            lstar_candidates++;
        }
    }

    /* Look for CR3-like values (physical PML4 address) */
    send_response(sock, "\n=== Searching for CR3 pattern ===\n");
    send_response(sock, "Expected: page-aligned physical address < 4GB\n\n");

    int cr3_candidates = 0;
    for (uint64_t offset = 0; offset < 0x200000 && cr3_candidates < 10; offset += 8) {
        uint64_t val = kernel_getlong(kdata_base + offset);

        /* CR3 should be page-aligned, non-zero, reasonable physical address */
        if ((val & 0xFFF) == 0 &&
            val > 0x100000 &&
            val < 0x100000000UL) {
            /* Verify it looks like a valid PML4 by checking entry 511 */
            uint64_t pml4e_511 = kernel_getlong(get_dmap_base() + val + (511 * 8));
            if (pml4e_511 & PTE_P) {
                send_response(sock, "Possible CR3 @ kdata+0x%lx: 0x%lx (PML4E[511]=0x%lx)\n",
                              offset, val, pml4e_511);
                cr3_candidates++;
            }
        }
    }

    send_response(sock, "OK\n");
}

/*
 * probe_signal_handler - Signal handler for fault-safe probing
 */
static void
probe_signal_handler(int sig)
{
    (void)sig;
    probe_fault_occurred = 1;
    siglongjmp(probe_jmp_env, 1);
}

/*
 * probe_dmap - Test DMAP physical address accessibility (fault-safe)
 * Usage: probe_dmap <start_paddr> <end_paddr> [stride]
 *
 * Uses signal handling to safely test if physical addresses
 * are readable via DMAP without causing kernel panic.
 *
 * WARNING: HV-triggered faults may not be catchable via signals.
 */
static void
cmd_probe_dmap(int sock, const char *args)
{
    unsigned long start_pa, end_pa, stride = 0x200000; /* 2MB default */
    struct sigaction sa, old_sigsegv, old_sigbus;
    uint64_t dmap_base = get_dmap_base();
    int accessible = 0, blocked = 0;
    int probed = 0;

    if (sscanf(args, "%lx %lx %lx", &start_pa, &end_pa, &stride) < 2) {
        send_response(sock, "Usage: probe_dmap <start_paddr> <end_paddr> [stride]\n");
        send_response(sock, "Example: probe_dmap 0 4000000 200000\n");
        return;
    }

    if (stride == 0) stride = 0x200000;
    if (end_pa <= start_pa) {
        send_response(sock, "ERROR: end_paddr must be > start_paddr\n");
        return;
    }

    /* Setup signal handlers for fault recovery */
    memset(&sa, 0, sizeof(sa));
    sa.sa_handler = probe_signal_handler;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = 0;

    sigaction(SIGSEGV, &sa, &old_sigsegv);
    sigaction(SIGBUS, &sa, &old_sigbus);

    send_response(sock, "=== DMAP Accessibility Probe: 0x%lx - 0x%lx ===\n",
                  start_pa, end_pa);
    send_response(sock, "DMAP base: 0x%lx, Stride: 0x%lx\n", dmap_base, stride);
    send_response(sock, "WARNING: HV faults may still cause panic!\n\n");

    for (uint64_t pa = start_pa; pa < end_pa && probed < 1024; pa += stride) {
        uint64_t va = dmap_base + pa;
        uint64_t val;

        probe_fault_occurred = 0;

        if (sigsetjmp(probe_jmp_env, 1) == 0) {
            /* Try to read - may fault */
            if (kernel_copyout(va, &val, sizeof(val)) == 0) {
                send_response(sock, "0x%012lx: READABLE (val=0x%016lx)\n", pa, val);
                accessible++;
            } else {
                send_response(sock, "0x%012lx: COPYOUT_FAILED\n", pa);
                blocked++;
            }
        } else {
            /* Returned from signal handler - fault occurred */
            send_response(sock, "0x%012lx: FAULT (signal caught)\n", pa);
            blocked++;
        }
        probed++;
    }

    /* Restore original signal handlers */
    sigaction(SIGSEGV, &old_sigsegv, NULL);
    sigaction(SIGBUS, &old_sigbus, NULL);

    send_response(sock, "\n=== Summary ===\n");
    send_response(sock, "Probed: %d, Accessible: %d, Blocked: %d\n",
                  probed, accessible, blocked);
    send_response(sock, "OK\n");
}

/*
 * apic_probe - Probe Local APIC registers via DMAP
 * Usage: apic_probe
 *
 * The APIC at physical 0xfee00000 is memory-mapped. If accessible:
 * - Could reveal HV interception patterns
 * - Understanding APIC virtualization is key for timing attacks
 */
static void
cmd_apic_probe(int sock)
{
    uint64_t dmap_base = get_dmap_base();
    uint64_t apic_paddr = DEFAULT_APIC_BASE;  /* 0xfee00000 */
    uint64_t apic_vaddr = dmap_base + apic_paddr;
    uint32_t val;

    /* APIC register offsets and names */
    struct {
        uint32_t offset;
        const char *name;
    } apic_regs[] = {
        {0x020, "LAPIC_ID"},
        {0x030, "LAPIC_VERSION"},
        {0x080, "TPR"},
        {0x090, "APR"},
        {0x0A0, "PPR"},
        {0x0B0, "EOI"},
        {0x0C0, "RRD"},
        {0x0D0, "LDR"},
        {0x0E0, "DFR"},
        {0x0F0, "SVR"},
        {0x100, "ISR0"},
        {0x200, "IRR0"},
        {0x280, "ESR"},
        {0x300, "ICR_LO"},
        {0x310, "ICR_HI"},
        {0x320, "LVT_TIMER"},
        {0x330, "LVT_THERMAL"},
        {0x340, "LVT_PERF"},
        {0x350, "LVT_LINT0"},
        {0x360, "LVT_LINT1"},
        {0x370, "LVT_ERROR"},
        {0x380, "TIMER_ICR"},
        {0x390, "TIMER_CCR"},
        {0x3E0, "TIMER_DCR"},
    };

    send_response(sock, "=== APIC Probe via DMAP ===\n");
    send_response(sock, "APIC physical: 0x%lx\n", apic_paddr);
    send_response(sock, "DMAP address: 0x%lx\n\n", apic_vaddr);
    send_response(sock, "WARNING: APIC access may be HV-virtualized or blocked\n\n");

    int readable = 0, failed = 0;

    for (int i = 0; i < (int)(sizeof(apic_regs)/sizeof(apic_regs[0])); i++) {
        uint64_t reg_addr = apic_vaddr + apic_regs[i].offset;

        if (kernel_copyout(reg_addr, &val, sizeof(val)) == 0) {
            send_response(sock, "%-12s [0x%03x]: 0x%08x\n",
                          apic_regs[i].name, apic_regs[i].offset, val);
            readable++;
        } else {
            send_response(sock, "%-12s [0x%03x]: READ FAILED\n",
                          apic_regs[i].name, apic_regs[i].offset);
            failed++;
        }
    }

    send_response(sock, "\n=== Analysis ===\n");
    send_response(sock, "Registers readable: %d, failed: %d\n", readable, failed);

    if (readable > 0) {
        send_response(sock, "\nAPIC is accessible via DMAP!\n");
        send_response(sock, "This could enable:\n");
        send_response(sock, "  - Timer-based side channel attacks\n");
        send_response(sock, "  - IPI injection analysis\n");
        send_response(sock, "  - HV interception timing measurements\n");
    } else {
        send_response(sock, "\nAPIC is NOT accessible - likely HV protected\n");
    }

    send_response(sock, "OK\n");
}

/*
 * apic_timing - Measure memory access timing using APIC timer
 * Usage: apic_timing
 *
 * Uses the APIC timer (CCR - Current Count Register) to measure
 * timing differences between accessible and blocked memory regions.
 * Large timing differences indicate HV intercept overhead.
 */
static void
cmd_apic_timing(int sock)
{
    uint64_t dmap_base = get_dmap_base();
    uint64_t apic_vaddr = dmap_base + DEFAULT_APIC_BASE;
    uint32_t timer_start, timer_end;
    uint64_t val;
    int i;

    #define APIC_CCR_OFFSET 0x390
    #define NUM_SAMPLES 10

    send_response(sock, "=== APIC Timing Analysis ===\n\n");
    send_response(sock, "DMAP base: 0x%lx\n", dmap_base);
    send_response(sock, "APIC CCR @ 0x%lx\n", apic_vaddr + APIC_CCR_OFFSET);
    send_response(sock, "Samples per test: %d\n\n", NUM_SAMPLES);

    /* Test 1: Time DMAP read of known accessible memory (.data region) */
    send_response(sock, "=== Test 1: Accessible Memory (DMAP .data) ===\n");
    uint64_t accessible_pa = 0x1000000;  /* 16MB - known accessible from scan */
    uint64_t accessible_va = dmap_base + accessible_pa;
    uint32_t accessible_times[NUM_SAMPLES];
    uint32_t accessible_total = 0;

    for (i = 0; i < NUM_SAMPLES; i++) {
        kernel_copyout(apic_vaddr + APIC_CCR_OFFSET, &timer_start, 4);
        kernel_copyout(accessible_va, &val, 8);
        kernel_copyout(apic_vaddr + APIC_CCR_OFFSET, &timer_end, 4);
        accessible_times[i] = timer_start - timer_end;
        accessible_total += accessible_times[i];
    }
    send_response(sock, "PA 0x%lx: ", accessible_pa);
    for (i = 0; i < NUM_SAMPLES; i++) {
        send_response(sock, "%u ", accessible_times[i]);
    }
    send_response(sock, "\nAverage: %u cycles\n\n", accessible_total / NUM_SAMPLES);

    /* Test 2: Time multiple accessible regions to establish baseline */
    send_response(sock, "=== Test 2: Multiple Accessible Regions ===\n");
    uint64_t test_addrs[] = {0x2000000, 0x4000000, 0x8000000, 0xA000000};
    for (int t = 0; t < 4; t++) {
        uint64_t test_va = dmap_base + test_addrs[t];
        uint32_t total = 0;
        for (i = 0; i < NUM_SAMPLES; i++) {
            kernel_copyout(apic_vaddr + APIC_CCR_OFFSET, &timer_start, 4);
            kernel_copyout(test_va, &val, 8);
            kernel_copyout(apic_vaddr + APIC_CCR_OFFSET, &timer_end, 4);
            total += timer_start - timer_end;
        }
        send_response(sock, "PA 0x%lx: avg %u cycles\n", test_addrs[t], total / NUM_SAMPLES);
    }

    /* Test 3: Time APIC register reads (known to work) */
    send_response(sock, "\n=== Test 3: APIC Register Read Timing ===\n");
    uint32_t apic_total = 0;
    for (i = 0; i < NUM_SAMPLES; i++) {
        kernel_copyout(apic_vaddr + APIC_CCR_OFFSET, &timer_start, 4);
        kernel_copyout(apic_vaddr + 0x020, &val, 4);  /* LAPIC_ID */
        kernel_copyout(apic_vaddr + APIC_CCR_OFFSET, &timer_end, 4);
        apic_total += timer_start - timer_end;
    }
    send_response(sock, "APIC register read: avg %u cycles\n", apic_total / NUM_SAMPLES);

    /* Test 4: Measure kernel_copyout overhead */
    send_response(sock, "\n=== Test 4: kernel_copyout Baseline ===\n");
    uint32_t overhead_total = 0;
    for (i = 0; i < NUM_SAMPLES; i++) {
        kernel_copyout(apic_vaddr + APIC_CCR_OFFSET, &timer_start, 4);
        /* Just two timer reads back-to-back */
        kernel_copyout(apic_vaddr + APIC_CCR_OFFSET, &timer_end, 4);
        overhead_total += timer_start - timer_end;
    }
    send_response(sock, "Timer read overhead: avg %u cycles\n", overhead_total / NUM_SAMPLES);

    send_response(sock, "\n=== Analysis ===\n");
    send_response(sock, "Baseline (timer overhead): ~%u cycles\n", overhead_total / NUM_SAMPLES);
    send_response(sock, "DMAP read adds: ~%u cycles\n",
                  (accessible_total / NUM_SAMPLES) - (overhead_total / NUM_SAMPLES));
    send_response(sock, "\nTo detect HV intercepts, compare these with reads to blocked regions.\n");
    send_response(sock, "Use 'map_xom_boundary' to find blocked region boundaries first.\n");
    send_response(sock, "OK\n");
}

/*
 * map_xom_boundary - Find exact boundaries of XOM-protected memory regions
 * Usage: map_xom_boundary [start_pa] [end_pa] [granularity]
 *
 * Does fine-grained probing to find exact start/end of blocked regions.
 * Default scans physical memory with 4KB granularity looking for transitions.
 */
static void
cmd_map_xom_boundary(int sock, const char *args)
{
    unsigned long start_pa = 0;
    unsigned long end_pa = 0x10000000;    /* 256MB default */
    unsigned long granularity = 0x1000;   /* 4KB default */
    uint64_t dmap_base = get_dmap_base();
    uint8_t dummy[8];
    int transitions = 0;
    int last_accessible = -1;  /* -1 = unknown, 0 = blocked, 1 = accessible */

    sscanf(args, "%lx %lx %lx", &start_pa, &end_pa, &granularity);

    if (granularity < 0x1000) granularity = 0x1000;  /* Minimum 4KB */
    if (end_pa <= start_pa) {
        send_response(sock, "Usage: map_xom_boundary [start_pa] [end_pa] [granularity]\n");
        send_response(sock, "Example: map_xom_boundary 0 10000000 1000\n");
        return;
    }

    /* Limit iterations to prevent timeout */
    unsigned long max_probes = (end_pa - start_pa) / granularity;
    if (max_probes > 65536) {
        send_response(sock, "WARNING: Limiting to 65536 probes. Increase granularity.\n");
        max_probes = 65536;
    }

    send_response(sock, "=== XOM Boundary Mapping ===\n");
    send_response(sock, "Range: 0x%lx - 0x%lx\n", start_pa, end_pa);
    send_response(sock, "Granularity: 0x%lx (%lu KB)\n", granularity, granularity / 1024);
    send_response(sock, "DMAP base: 0x%lx\n\n", dmap_base);
    send_response(sock, "Scanning for accessible/blocked transitions...\n\n");

    uint64_t first_blocked = 0, last_blocked = 0;
    int blocked_count = 0, accessible_count = 0;

    for (uint64_t pa = start_pa; pa < end_pa && transitions < 100; pa += granularity) {
        uint64_t va = dmap_base + pa;
        int is_accessible = (kernel_copyout(va, dummy, sizeof(dummy)) == 0);

        if (last_accessible != -1 && is_accessible != last_accessible) {
            /* Found a transition */
            if (is_accessible) {
                send_response(sock, "TRANSITION @ PA 0x%lx: BLOCKED -> ACCESSIBLE\n", pa);
                last_blocked = pa - granularity;
            } else {
                send_response(sock, "TRANSITION @ PA 0x%lx: ACCESSIBLE -> BLOCKED\n", pa);
                if (first_blocked == 0) first_blocked = pa;
            }
            transitions++;
        }

        if (is_accessible) {
            accessible_count++;
        } else {
            blocked_count++;
            if (first_blocked == 0) first_blocked = pa;
            last_blocked = pa;
        }

        last_accessible = is_accessible;
    }

    send_response(sock, "\n=== Summary ===\n");
    send_response(sock, "Probes: accessible=%d, blocked=%d\n", accessible_count, blocked_count);
    send_response(sock, "Transitions found: %d\n", transitions);

    if (blocked_count > 0) {
        send_response(sock, "\n=== Blocked Region Estimate ===\n");
        send_response(sock, "First blocked: PA 0x%lx (DMAP 0x%lx)\n",
                      first_blocked, dmap_base + first_blocked);
        send_response(sock, "Last blocked:  PA 0x%lx (DMAP 0x%lx)\n",
                      last_blocked, dmap_base + last_blocked);
        send_response(sock, "Approx size:   0x%lx (%lu MB)\n",
                      last_blocked - first_blocked,
                      (last_blocked - first_blocked) / (1024 * 1024));
        send_response(sock, "\nFor finer mapping, run:\n");
        send_response(sock, "  map_xom_boundary %lx %lx 1000\n",
                      first_blocked > 0x100000 ? first_blocked - 0x100000 : 0,
                      last_blocked + 0x100000);
    }

    send_response(sock, "OK\n");
}

/* Comparison function for qsort */
static int
cmp_uint64(const void *a, const void *b)
{
    uint64_t va = *(const uint64_t *)a;
    uint64_t vb = *(const uint64_t *)b;
    if (va < vb) return -1;
    if (va > vb) return 1;
    return 0;
}

/*
 * timing_probe - Accurate timing measurement for specific physical address
 * Usage: timing_probe <paddr> [samples]
 *
 * Measures memory access timing with proper wraparound handling.
 * Reports min/max/median/avg statistics. Median is robust to outliers.
 */
static void
cmd_timing_probe(int sock, const char *args)
{
    unsigned long paddr = 0;
    int num_samples = 50;
    uint64_t dmap_base = get_dmap_base();
    uint64_t apic_vaddr = dmap_base + DEFAULT_APIC_BASE;
    uint32_t timer_start, timer_end;
    uint64_t val;

    if (sscanf(args, "%lx %d", &paddr, &num_samples) < 1) {
        send_response(sock, "Usage: timing_probe <paddr> [samples]\n");
        send_response(sock, "Example: timing_probe a6ff000 50\n");
        return;
    }

    if (num_samples < 1) num_samples = 1;
    if (num_samples > 100) num_samples = 100;

    uint64_t va = dmap_base + paddr;
    uint64_t times[100];
    uint64_t min_time = UINT64_MAX, max_time = 0, total = 0;
    int successes = 0, failures = 0;

    send_response(sock, "=== Timing Probe: PA 0x%lx ===\n", paddr);
    send_response(sock, "DMAP VA: 0x%lx\n", va);
    send_response(sock, "Samples: %d\n\n", num_samples);

    /* First check if address is accessible */
    uint8_t test_buf[8];
    if (kernel_copyout(va, test_buf, sizeof(test_buf)) != 0) {
        send_response(sock, "WARNING: Address appears BLOCKED (kernel_copyout failed)\n");
        send_response(sock, "Timing blocked addresses may cause issues.\n\n");
    }

    send_response(sock, "Raw timings: ");
    for (int i = 0; i < num_samples; i++) {
        kernel_copyout(apic_vaddr + 0x390, &timer_start, 4);  /* CCR */
        int result = kernel_copyout(va, &val, 8);
        kernel_copyout(apic_vaddr + 0x390, &timer_end, 4);

        if (result != 0) {
            failures++;
            times[i] = UINT64_MAX;  /* Mark failed reads */
            continue;
        }
        successes++;

        /* Handle timer wraparound (CCR counts down) */
        uint64_t delta;
        if (timer_end > timer_start) {
            /* Timer wrapped around */
            delta = (uint64_t)timer_start + (0x100000000ULL - (uint64_t)timer_end);
        } else {
            delta = timer_start - timer_end;
        }

        times[i] = delta;
        total += delta;
        if (delta < min_time) min_time = delta;
        if (delta > max_time) max_time = delta;

        /* Print first 20 raw values */
        if (i < 20) {
            send_response(sock, "%lu ", (unsigned long)delta);
        }
    }
    send_response(sock, "%s\n", num_samples > 20 ? "..." : "");

    send_response(sock, "\n=== Statistics ===\n");
    if (successes > 0) {
        /* Sort times to get median */
        qsort(times, num_samples, sizeof(uint64_t), cmp_uint64);

        /* Find median (skip UINT64_MAX entries which are at the end after sort) */
        uint64_t median = times[successes / 2];

        uint64_t avg = total / successes;
        send_response(sock, "Successful reads: %d/%d\n", successes, num_samples);
        send_response(sock, "Min:     %lu cycles\n", (unsigned long)min_time);
        send_response(sock, "Median:  %lu cycles  <-- use this (robust to outliers)\n", (unsigned long)median);
        send_response(sock, "Average: %lu cycles\n", (unsigned long)avg);
        send_response(sock, "Max:     %lu cycles\n", (unsigned long)max_time);

        /* Classify based on MEDIAN, not average */
        if (median < 200) {
            send_response(sock, "\nClassification: NORMAL (fast DMAP access)\n");
        } else if (median < 10000) {
            send_response(sock, "\nClassification: SLOW (possible cache miss or contention)\n");
        } else {
            send_response(sock, "\nClassification: VERY SLOW (possible HV intercept or MMIO)\n");
        }
    } else {
        send_response(sock, "All reads FAILED - address is blocked\n");
    }

    if (failures > 0) {
        send_response(sock, "Failed reads: %d\n", failures);
    }

    send_response(sock, "OK\n");
}

/*
 * timing_boundary - Time reads at XOM boundary edges
 * Usage: timing_boundary
 *
 * Uses known XOM boundaries from map_xom_boundary to measure
 * timing differences near the protected region.
 * Uses MEDIAN for robust statistics (immune to timer wraparound outliers).
 */
static void
cmd_timing_boundary(int sock)
{
    uint64_t dmap_base = get_dmap_base();
    uint64_t apic_vaddr = dmap_base + DEFAULT_APIC_BASE;
    uint32_t timer_start, timer_end;
    uint64_t val;

    /* Known XOM boundaries from map_xom_boundary results */
    /* These are for FW 4.03 - may differ on other versions */
    uint64_t xom_start = 0xa700000;    /* First blocked PA */
    uint64_t xom_end = 0xb300000;      /* First accessible after XOM */

    /* Test points */
    struct {
        uint64_t paddr;
        const char *desc;
    } test_points[] = {
        {0x8000000,         "8MB - well before XOM"},
        {0xa000000,         "160MB - anomaly region"},
        {xom_start - 0x2000, "XOM-8KB (2 pages before)"},
        {xom_start - 0x1000, "XOM-4KB (1 page before)"},
        {xom_start,          "XOM start (BLOCKED)"},
        {xom_end,            "XOM end (first accessible)"},
        {xom_end + 0x1000,   "XOM+4KB (1 page after)"},
        {0xc000000,         "192MB - well after XOM"},
    };

    int num_points = sizeof(test_points) / sizeof(test_points[0]);
    int samples = 50;  /* More samples for better median */

    send_response(sock, "=== XOM Boundary Timing Analysis ===\n");
    send_response(sock, "XOM region: PA 0x%lx - 0x%lx\n", xom_start, xom_end);
    send_response(sock, "Samples per point: %d (using MEDIAN)\n\n", samples);
    send_response(sock, "%-30s %-12s %-10s %-10s %-10s\n",
                  "Location", "PA", "Min", "Median", "Status");
    send_response(sock, "--------------------------------------------------------------------\n");

    for (int t = 0; t < num_points; t++) {
        uint64_t paddr = test_points[t].paddr;
        uint64_t va = dmap_base + paddr;

        uint64_t times[50];
        uint64_t min_time = UINT64_MAX;
        int successes = 0;

        for (int i = 0; i < samples; i++) {
            kernel_copyout(apic_vaddr + 0x390, &timer_start, 4);
            int result = kernel_copyout(va, &val, 8);
            kernel_copyout(apic_vaddr + 0x390, &timer_end, 4);

            if (result != 0) {
                times[i] = UINT64_MAX;
                continue;
            }
            successes++;

            uint64_t delta;
            if (timer_end > timer_start) {
                delta = (uint64_t)timer_start + (0x100000000ULL - (uint64_t)timer_end);
            } else {
                delta = timer_start - timer_end;
            }

            times[i] = delta;
            if (delta < min_time) min_time = delta;
        }

        if (successes > 0) {
            /* Sort to get median */
            qsort(times, samples, sizeof(uint64_t), cmp_uint64);
            uint64_t median = times[successes / 2];

            const char *status = (median < 200) ? "FAST" :
                                 (median < 10000) ? "SLOW" : "VERY SLOW";
            send_response(sock, "%-30s 0x%-10lx %-10lu %-10lu %s\n",
                          test_points[t].desc, paddr,
                          (unsigned long)min_time, (unsigned long)median, status);
        } else {
            send_response(sock, "%-30s 0x%-10lx %-10s %-10s BLOCKED\n",
                          test_points[t].desc, paddr, "-", "-");
        }
    }

    send_response(sock, "\n=== Analysis ===\n");
    send_response(sock, "Compare timing at XOM-4KB vs 8MB baseline.\n");
    send_response(sock, "If similar (~140-180 cycles), no HV pre-emptive checking.\n");
    send_response(sock, "OK\n");
}

/*
 * verify_xom - Re-verify XOM boundaries with detailed analysis
 * Usage: verify_xom
 *
 * Performs thorough check of XOM region to confirm boundaries
 * and detect any anomalies from previous scans.
 */
static void
cmd_verify_xom(int sock)
{
    uint64_t dmap_base = get_dmap_base();

    /* Expected XOM boundaries from previous map_xom_boundary */
    uint64_t expected_start = 0xa700000;
    uint64_t expected_end = 0xb300000;

    send_response(sock, "=== XOM Boundary Verification ===\n");
    send_response(sock, "Expected XOM: PA 0x%lx - 0x%lx\n\n", expected_start, expected_end);

    /* Test points around boundaries */
    struct {
        uint64_t paddr;
        const char *desc;
        int expect_blocked;
    } tests[] = {
        {expected_start - 0x2000, "2 pages before XOM", 0},
        {expected_start - 0x1000, "1 page before XOM", 0},
        {expected_start,          "XOM start", 1},
        {expected_start + 0x1000, "XOM start + 4KB", 1},
        {expected_start + 0x100000, "XOM start + 1MB", 1},
        {expected_end - 0x1000,   "XOM end - 4KB", 1},
        {expected_end,            "XOM end", 0},
        {expected_end + 0x1000,   "1 page after XOM", 0},
    };

    int num_tests = sizeof(tests) / sizeof(tests[0]);
    int passed = 0, failed = 0;

    send_response(sock, "%-25s %-12s %-10s %-10s %-10s\n",
                  "Location", "PA", "Expected", "Actual", "Result");
    send_response(sock, "---------------------------------------------------------------\n");

    for (int i = 0; i < num_tests; i++) {
        uint64_t va = dmap_base + tests[i].paddr;
        uint8_t buf[8];

        /* Try multiple reads to be sure */
        int blocked_count = 0;
        for (int j = 0; j < 5; j++) {
            if (kernel_copyout(va, buf, sizeof(buf)) != 0) {
                blocked_count++;
            }
        }

        int is_blocked = (blocked_count >= 3);  /* Majority vote */
        int expected = tests[i].expect_blocked;
        int match = (is_blocked == expected);

        const char *exp_str = expected ? "BLOCKED" : "OK";
        const char *act_str = is_blocked ? "BLOCKED" : "OK";
        const char *res_str = match ? "PASS" : "FAIL";

        send_response(sock, "%-25s 0x%-10lx %-10s %-10s %-10s\n",
                      tests[i].desc, tests[i].paddr, exp_str, act_str, res_str);

        if (match) passed++;
        else failed++;
    }

    send_response(sock, "\n=== Summary ===\n");
    send_response(sock, "Passed: %d/%d\n", passed, num_tests);

    if (failed > 0) {
        send_response(sock, "FAILED: %d - XOM boundaries may have changed!\n", failed);
        send_response(sock, "Run 'map_xom_boundary' to re-scan.\n");
    } else {
        send_response(sock, "All tests passed - XOM boundaries confirmed.\n");
    }

    /* Also show APIC timer state */
    uint64_t apic_vaddr = dmap_base + DEFAULT_APIC_BASE;
    uint32_t icr, ccr, dcr;

    kernel_copyout(apic_vaddr + 0x380, &icr, 4);  /* Initial Count */
    kernel_copyout(apic_vaddr + 0x390, &ccr, 4);  /* Current Count */
    kernel_copyout(apic_vaddr + 0x3e0, &dcr, 4);  /* Divide Config */

    send_response(sock, "\n=== APIC Timer State ===\n");
    send_response(sock, "ICR (Initial Count):  0x%08x (%u)\n", icr, icr);
    send_response(sock, "CCR (Current Count):  0x%08x (%u)\n", ccr, ccr);
    send_response(sock, "DCR (Divide Config):  0x%08x\n", dcr);

    if (icr == 0) {
        send_response(sock, "WARNING: ICR=0 means timer is not running in periodic mode.\n");
        send_response(sock, "Timer wraparound happens whenever CCR reaches 0.\n");
    } else {
        send_response(sock, "Timer period: %u cycles before wraparound.\n", icr);
    }

    send_response(sock, "OK\n");
}

/*
 * scan_apic_ops - Search for apic_ops and similar function pointer tables
 * Usage: scan_apic_ops [min_ptrs]
 *
 * Scans kernel .data for consecutive pointers into .text range.
 * The apic_ops structure contains function pointers that can be
 * hijacked during suspend/resume to execute code before HV restarts.
 */
static void
cmd_scan_apic_ops(int sock, const char *args)
{
    intptr_t kdata_base = KERNEL_ADDRESS_DATA_BASE;
    intptr_t ktext_base = KERNEL_ADDRESS_TEXT_BASE;

    /* Scan parameters */
    int min_ptrs = 4;  /* Minimum consecutive pointers to report */
    if (args && *args) {
        sscanf(args, "%d", &min_ptrs);
    }
    if (min_ptrs < 2) min_ptrs = 2;
    if (min_ptrs > 20) min_ptrs = 20;

    /* Define kernel .text range (approximate) */
    uint64_t text_start = (uint64_t)ktext_base;
    uint64_t text_end = text_start + 0x1000000;  /* ~16MB .text */

    /* Scan range in .data */
    uint64_t scan_start = (uint64_t)kdata_base;
    uint64_t scan_size = 0x1000000;  /* Scan 16MB of .data */

    send_response(sock, "=== Scanning for Function Pointer Tables ===\n");
    send_response(sock, "Looking for %d+ consecutive .text pointers in .data\n", min_ptrs);
    send_response(sock, ".text range: 0x%lx - 0x%lx\n", text_start, text_end);
    send_response(sock, ".data scan:  0x%lx - 0x%lx\n\n", scan_start, scan_start + scan_size);

    int tables_found = 0;
    uint64_t addr = scan_start;

    while (addr < scan_start + scan_size - (min_ptrs * 8)) {
        /* Read a qword */
        uint64_t val;
        if (kernel_copyout(addr, &val, sizeof(val)) != 0) {
            addr += 8;
            continue;
        }

        /* Check if it's a .text pointer */
        if (val >= text_start && val < text_end) {
            /* Found a potential start - count consecutive pointers */
            int count = 1;
            uint64_t ptrs[20];
            ptrs[0] = val;

            for (int i = 1; i < 20; i++) {
                uint64_t next_val;
                if (kernel_copyout(addr + i * 8, &next_val, sizeof(next_val)) != 0) {
                    break;
                }
                if (next_val >= text_start && next_val < text_end) {
                    ptrs[i] = next_val;
                    count++;
                } else {
                    break;
                }
            }

            if (count >= min_ptrs) {
                tables_found++;
                uint64_t offset = addr - (uint64_t)kdata_base;
                send_response(sock, "=== Table #%d at kdata+0x%lx (VA 0x%lx) ===\n",
                              tables_found, offset, addr);
                send_response(sock, "Consecutive .text pointers: %d\n", count);

                for (int i = 0; i < count && i < 10; i++) {
                    uint64_t ptr_offset = ptrs[i] - text_start;
                    send_response(sock, "  [%d] 0x%lx (ktext+0x%lx)\n", i, ptrs[i], ptr_offset);
                }
                if (count > 10) {
                    send_response(sock, "  ... and %d more\n", count - 10);
                }
                send_response(sock, "\n");

                /* Skip past this table */
                addr += count * 8;
                continue;
            }
        }
        addr += 8;
    }

    send_response(sock, "=== Summary ===\n");
    send_response(sock, "Tables found: %d\n", tables_found);

    if (tables_found > 0) {
        send_response(sock, "\nTo exploit apic_ops:\n");
        send_response(sock, "1. Identify which table is apic_ops (look for ~10-15 ptrs)\n");
        send_response(sock, "2. Find a ROP gadget that passes CFI\n");
        send_response(sock, "3. Overwrite a function pointer (e.g., index 0 or 1)\n");
        send_response(sock, "4. Trigger suspend/resume cycle\n");
        send_response(sock, "5. Code executes before HV restarts\n");
    }

    send_response(sock, "OK\n");
}

/*
 * identify_table - Dump detailed context around a function pointer table
 * Usage: identify_table <va> [context_bytes]
 *
 * Shows hex+ASCII dump before/after, pointer spread analysis,
 * and nearby printable strings to help identify the structure.
 */
static void
cmd_identify_table(int sock, const char *args)
{
    unsigned long va;
    int context = 128;

    if (!args || !*args) {
        send_response(sock, "Usage: identify_table <addr> [context_bytes]\n");
        send_response(sock, "  addr - kdata offset (e.g. 179180) or full VA\n");
        send_response(sock, "  ctx  - bytes before/after to show (default 128, max 512)\n");
        send_response(sock, "\nUse kdata offsets from scan_apic_ops output.\n");
        return;
    }

    /* Parse address: if < 0x10000000, treat as kdata offset */
    unsigned long addr;
    if (sscanf(args, "%lx %d", &addr, &context) < 1) {
        send_response(sock, "ERROR: cannot parse address\n");
        return;
    }
    if (addr < 0x10000000) {
        va = (unsigned long)KERNEL_ADDRESS_DATA_BASE + addr;
        send_response(sock, "(kdata+0x%lx -> VA 0x%lx)\n", addr, va);
    } else {
        va = addr;
    }
    if (context < 32) context = 32;
    if (context > 512) context = 512;

    intptr_t ktext_base = KERNEL_ADDRESS_TEXT_BASE;
    intptr_t kdata_base = KERNEL_ADDRESS_DATA_BASE;
    uint64_t text_start = (uint64_t)ktext_base;
    uint64_t text_end = text_start + 0x1000000;

    /* 1. Count table entries (consecutive .text pointers at va) */
    int num_ptrs = 0;
    uint64_t ptrs[32];
    for (int i = 0; i < 32; i++) {
        uint64_t val;
        if (kernel_copyout(va + i * 8, &val, 8) != 0) break;
        if (val >= text_start && val < text_end) {
            ptrs[i] = val;
            num_ptrs++;
        } else {
            break;
        }
    }

    uint64_t kdata_off = (uint64_t)va - (uint64_t)kdata_base;
    send_response(sock, "=== Table at VA 0x%lx (kdata+0x%lx) ===\n", va, kdata_off);
    send_response(sock, "Consecutive .text pointers: %d\n\n", num_ptrs);

    /* 2. Dump pre-table context (hex + ASCII) */
    send_response(sock, "--- %d bytes BEFORE table ---\n", context);
    uint8_t buf[512];
    if (kernel_copyout(va - context, buf, context) == 0) {
        for (int i = 0; i < context; i += 16) {
            send_response(sock, "  %+5d: ", i - context);
            for (int j = 0; j < 16 && (i + j) < context; j++)
                send_response(sock, "%02x ", buf[i + j]);
            send_response(sock, " |");
            for (int j = 0; j < 16 && (i + j) < context; j++) {
                char c = buf[i + j];
                send_response(sock, "%c", (c >= 0x20 && c < 0x7f) ? c : '.');
            }
            send_response(sock, "|\n");
        }
    } else {
        send_response(sock, "  (read failed)\n");
    }

    /* 3. Dump table entries with analysis */
    send_response(sock, "\n--- Table entries ---\n");
    uint64_t min_off = UINT64_MAX, max_off = 0;
    for (int i = 0; i < num_ptrs; i++) {
        uint64_t off = ptrs[i] - text_start;
        if (off < min_off) min_off = off;
        if (off > max_off) max_off = off;
        send_response(sock, "  [%2d] 0x%lx  (ktext+0x%lx)\n", i, ptrs[i], off);
    }

    /* 4. Dump post-table context */
    send_response(sock, "\n--- %d bytes AFTER table ---\n", context);
    if (kernel_copyout(va + num_ptrs * 8, buf, context) == 0) {
        for (int i = 0; i < context; i += 16) {
            send_response(sock, "  %+5d: ", num_ptrs * 8 + i);
            for (int j = 0; j < 16 && (i + j) < context; j++)
                send_response(sock, "%02x ", buf[i + j]);
            send_response(sock, " |");
            for (int j = 0; j < 16 && (i + j) < context; j++) {
                char c = buf[i + j];
                send_response(sock, "%c", (c >= 0x20 && c < 0x7f) ? c : '.');
            }
            send_response(sock, "|\n");
        }
    } else {
        send_response(sock, "  (read failed)\n");
    }

    /* 5. Pointer spread analysis */
    send_response(sock, "\n--- Analysis ---\n");
    if (num_ptrs > 0) {
        send_response(sock, "Pointer range: ktext+0x%lx - ktext+0x%lx\n", min_off, max_off);
        send_response(sock, "Spread: 0x%lx (%lu bytes)\n", max_off - min_off, max_off - min_off);
        send_response(sock, "Table size: %d entries (%d bytes)\n", num_ptrs, num_ptrs * 8);

        /* Heuristic match for apic_ops */
        if (num_ptrs >= 10 && num_ptrs <= 16 && (max_off - min_off) < 0x1000) {
            send_response(sock, "\n** STRONG apic_ops candidate **\n");
            send_response(sock, "Matches: 10-16 ptrs, tightly clustered (<4KB spread)\n");
        }
    } else {
        send_response(sock, "No .text pointers found at this address.\n");
    }

    /* 6. Search for printable strings in wider context (512 bytes around) */
    send_response(sock, "\n--- Nearby strings (512B scan) ---\n");
    uint8_t wide[512];
    int found_strings = 0;
    if (kernel_copyout(va - 256, wide, 512) == 0) {
        for (int i = 0; i < 512; ) {
            if (wide[i] >= 0x20 && wide[i] < 0x7f) {
                int start = i;
                while (i < 512 && wide[i] >= 0x20 && wide[i] < 0x7f) i++;
                int len = i - start;
                if (len >= 4) {
                    found_strings++;
                    send_response(sock, "  offset %+d: \"", start - 256);
                    for (int j = start; j < start + len && j < start + 64; j++)
                        send_response(sock, "%c", wide[j]);
                    if (len > 64)
                        send_response(sock, "...");
                    send_response(sock, "\"\n");
                }
            } else {
                i++;
            }
        }
    }
    if (found_strings == 0) {
        send_response(sock, "  (no printable strings found)\n");
    }

    send_response(sock, "OK\n");
}

/*
 * FreeBSD apic_ops field names (31 known + potential PS5 extensions)
 */
static const char *apic_ops_fields[] = {
    "create", "init", "xapic_mode ***", "is_x2apic",
    "setup", "dump", "disable", "eoi",
    "id", "intr_pending", "set_logical_id", "cpuid",
    "alloc_vector", "alloc_vectors", "enable_vector", "disable_vector",
    "free_vector", "enable_pmc", "disable_pmc", "reenable_pmc",
    "enable_cmc", "enable_mca_elvt",
    "ipi_raw", "ipi_vectored", "ipi_wait", "ipi_alloc", "ipi_free",
    "set_lvt_mask", "set_lvt_mode", "set_lvt_polarity", "set_lvt_triggermode",
    NULL
};

/*
 * analyze_apic_ops - Full analysis of candidate apic_ops structure
 * Usage: analyze_apic_ops <kdata_offset>
 *
 * Reads 36 qwords, classifies each entry, maps to FreeBSD field names,
 * and searches for cross-references in .data.
 */
static void
cmd_analyze_apic_ops(int sock, const char *args)
{
    unsigned long offset;
    if (!args || sscanf(args, "%lx", &offset) != 1) {
        send_response(sock, "Usage: analyze_apic_ops <kdata_offset>\n");
        send_response(sock, "  e.g. analyze_apic_ops 179180\n");
        return;
    }

    intptr_t kdata_base = KERNEL_ADDRESS_DATA_BASE;
    intptr_t ktext_base = KERNEL_ADDRESS_TEXT_BASE;
    uint64_t va = (uint64_t)kdata_base + offset;
    uint64_t text_start = (uint64_t)ktext_base;
    uint64_t text_end = text_start + 0x1000000;
    uint64_t data_start = (uint64_t)kdata_base;
    uint64_t data_end = data_start + 0x4000000;

    int num_entries = 36;
    uint64_t entries[36];

    send_response(sock, "=== analyze_apic_ops at kdata+0x%lx (VA 0x%lx) ===\n\n",
                  offset, va);

    /* Read all 36 qwords */
    if (kernel_copyout(va, entries, num_entries * 8) != 0) {
        send_response(sock, "ERROR: failed to read %d bytes at 0x%lx\n",
                      num_entries * 8, va);
        return;
    }

    int text_count = 0, null_count = 0, data_count = 0, other_count = 0;

    send_response(sock, "--- Entries (36 qwords) ---\n");
    for (int i = 0; i < num_entries; i++) {
        uint64_t val = entries[i];
        const char *field;
        const char *type;

        /* Find field name - walk NULL-terminated array */
        int fi = 0;
        const char **fp = apic_ops_fields;
        while (*fp && fi < i) { fp++; fi++; }
        field = (fi == i && *fp) ? *fp : "(ps5 ext?)";

        if (val == 0) {
            type = "NULL";
            null_count++;
        } else if (val >= text_start && val < text_end) {
            type = ".text";
            text_count++;
        } else if (val >= data_start && val < data_end) {
            type = ".data";
            data_count++;
        } else {
            type = "other";
            other_count++;
        }

        if (val >= text_start && val < text_end) {
            send_response(sock, "  [%2d] %-22s 0x%lx  (ktext+0x%lx)  %s\n",
                          i, field, val, val - text_start, type);
        } else {
            send_response(sock, "  [%2d] %-22s 0x%016lx                %s\n",
                          i, field, val, type);
        }
    }

    /* Summary */
    send_response(sock, "\n--- Summary ---\n");
    send_response(sock, ".text ptrs: %d  NULL: %d  .data ptrs: %d  other: %d\n",
                  text_count, null_count, data_count, other_count);

    if (text_count >= 20) {
        send_response(sock, "\n** STRONG apic_ops match (%d/36 .text ptrs) **\n",
                      text_count);
    } else if (text_count >= 10) {
        send_response(sock, "\n* Possible apic_ops (%d/36 .text ptrs) *\n",
                      text_count);
    }

    /* Cross-reference scan: search for pointers TO this table in .data */
    send_response(sock, "\n--- Cross-references (ptrs to 0x%lx in .data) ---\n", va);
    int xrefs = 0;
    uint64_t scan_addr = data_start;
    uint64_t scan_end = data_start + 0x1000000;  /* scan 16MB */
    uint8_t scan_buf[4096];

    while (scan_addr < scan_end) {
        if (kernel_copyout(scan_addr, scan_buf, sizeof(scan_buf)) != 0) {
            scan_addr += sizeof(scan_buf);
            continue;
        }
        for (int i = 0; i <= (int)sizeof(scan_buf) - 8; i += 8) {
            uint64_t val;
            memcpy(&val, scan_buf + i, 8);
            if (val == va) {
                uint64_t ref_off = (scan_addr + i) - data_start;
                send_response(sock, "  Found at kdata+0x%lx (VA 0x%lx)\n",
                              ref_off, scan_addr + i);
                xrefs++;
            }
        }
        scan_addr += sizeof(scan_buf);
    }
    if (xrefs == 0) {
        send_response(sock,
            "  (none found - table may be inline, not referenced by pointer)\n");
    } else {
        send_response(sock, "  Total: %d cross-references\n", xrefs);
    }

    /* Highlight xapic_mode entry */
    if (entries[2] >= text_start && entries[2] < text_end) {
        send_response(sock, "\n*** xapic_mode (entry [2]) = ktext+0x%lx ***\n",
                      entries[2] - text_start);
        send_response(sock, "This is the resume-time target for HV bypass.\n");
        send_response(sock, "Overwrite VA 0x%lx (kdata+0x%lx) with ROP gadget.\n",
                      va + 16, offset + 16);
    }

    send_response(sock, "OK\n");
}

/*
 * find_cfi_targets - Find CFI-valid void(*)(void) function targets
 *
 * Since .text is XOM we can't scan for gadgets directly. Instead, we collect
 * all unique function pointers from ops tables in .data. Functions used as
 * void(*)(void) entries share the same Clang CFI type hash as xapic_mode,
 * making them valid replacement targets.
 *
 * Strategy:
 * 1. Scan .data for function pointer tables (like scan_apic_ops)
 * 2. For each table, collect entries at indices known to be void(*)(void)
 * 3. Also collect ALL unique .text pointers as potential targets
 * 4. Report sorted by .text offset for cross-referencing
 */
static void
cmd_find_cfi_targets(int sock)
{
    intptr_t kdata_base = KERNEL_ADDRESS_DATA_BASE;
    intptr_t ktext_base = KERNEL_ADDRESS_TEXT_BASE;
    uint64_t text_start = (uint64_t)ktext_base;
    uint64_t text_end = text_start + 0x1000000;
    uint64_t scan_start = (uint64_t)kdata_base;
    uint64_t scan_size = 0x1000000;  /* 16MB of .data */

    send_response(sock, "=== Finding CFI-valid targets for void(*)(void) ===\n\n");

    /*
     * Phase 1: Collect unique .text pointers from .data with ref counts.
     * Max 4096 unique pointers should be plenty.
     */
    #define MAX_TARGETS 4096
    uint64_t *targets = __builtin_alloca(MAX_TARGETS * sizeof(uint64_t));
    int *refcounts = __builtin_alloca(MAX_TARGETS * sizeof(int));
    int num_targets = 0;

    send_response(sock, "Scanning 16MB of .data for .text pointers...\n");

    uint64_t addr = scan_start;
    uint8_t buf[4096];

    while (addr < scan_start + scan_size) {
        if (kernel_copyout(addr, buf, sizeof(buf)) != 0) {
            addr += sizeof(buf);
            continue;
        }

        for (int i = 0; i <= (int)sizeof(buf) - 8; i += 8) {
            uint64_t val;
            memcpy(&val, buf + i, 8);

            if (val >= text_start && val < text_end) {
                /* Check for duplicate, increment refcount */
                int found = -1;
                for (int j = 0; j < num_targets; j++) {
                    if (targets[j] == val) {
                        found = j;
                        break;
                    }
                }
                if (found >= 0) {
                    refcounts[found]++;
                } else if (num_targets < MAX_TARGETS) {
                    targets[num_targets] = val;
                    refcounts[num_targets] = 1;
                    num_targets++;
                }
            }
        }
        addr += sizeof(buf);
    }

    send_response(sock, "Found %d unique .text pointers in .data\n\n", num_targets);

    /* Sort by address using simple insertion sort (move refcounts too) */
    for (int i = 1; i < num_targets; i++) {
        uint64_t key = targets[i];
        int key_ref = refcounts[i];
        int j = i - 1;
        while (j >= 0 && targets[j] > key) {
            targets[j + 1] = targets[j];
            refcounts[j + 1] = refcounts[j];
            j--;
        }
        targets[j + 1] = key;
        refcounts[j + 1] = key_ref;
    }

    /*
     * Phase 2: Identify likely void(*)(void) targets
     *
     * In apic_ops, these indices are void(*)(void):
     *   [2] xapic_mode, [6] disable, [7] eoi
     *
     * We know the apic_ops at kdata+0x179180. Read those specific entries
     * as confirmed void(*)(void) targets.
     */
    send_response(sock, "--- Confirmed void(*)(void) from apic_ops ---\n");

    uint64_t apic_ops_va = (uint64_t)kdata_base + 0x179180;
    /* Indices known to be void(*)(void): xapic_mode, disable, eoi */
    int void_indices[] = {2, 6, 7};
    int num_void = sizeof(void_indices) / sizeof(void_indices[0]);

    for (int v = 0; v < num_void; v++) {
        uint64_t fptr;
        if (kernel_copyout(apic_ops_va + void_indices[v] * 8, &fptr, 8) == 0) {
            if (fptr >= text_start && fptr < text_end) {
                send_response(sock, "  apic_ops[%d] = ktext+0x%lx  (confirmed void(*)(void))\n",
                              void_indices[v], fptr - text_start);
            }
        }
    }

    /*
     * Phase 3: Show frequently-referenced .text functions (3+ refs)
     * Functions appearing many times in .data are likely common ops callbacks.
     * Uses refcounts collected during Phase 1 scan (no re-scanning).
     */
    send_response(sock, "\n--- Frequently referenced .text functions (3+ refs) ---\n");
    send_response(sock, "(Functions used in multiple places more likely to be simple callbacks)\n\n");

    int freq_count = 0;
    for (int i = 0; i < num_targets; i++) {
        if (refcounts[i] >= 3) {
            send_response(sock, "  ktext+0x%06lx  refs=%d\n",
                          targets[i] - text_start, refcounts[i]);
            freq_count++;
        }
    }
    send_response(sock, "Total: %d frequently-referenced functions\n", freq_count);

    /*
     * Phase 4: Summary of all unique .text targets
     */
    send_response(sock, "\n--- All unique .text pointers (%d total) ---\n", num_targets);
    send_response(sock, "(Sorted by ktext offset, any could be a CFI target)\n\n");

    for (int i = 0; i < num_targets; i++) {
        uint64_t off = targets[i] - text_start;
        send_response(sock, "  ktext+0x%06lx\n", off);
    }

    send_response(sock, "\n--- Next steps ---\n");
    send_response(sock, "1. Confirmed void(*)(void): apic_ops entries [2],[6],[7]\n");
    send_response(sock, "2. Any function above could pass CFI if type-hash matches\n");
    send_response(sock, "3. For stack pivot: need func that uses controlled reg as memop\n");
    send_response(sock, "4. Cross-ref offsets with known FW 4.03 kernel binary\n");
    send_response(sock, "OK\n");
}

/*
 * IDT Discovery Helpers
 *
 * The PS5 hypervisor blocks SIDT (kernel panic) and the cached IDTR
 * structure is not stored in .data. Instead we find the IDT by scanning
 * .data/.bss for a contiguous block of valid x86-64 gate descriptors.
 */

/* Validate a single 16-byte gate descriptor entry */
static int
is_valid_idt_gate(const uint8_t *e, uint64_t ktext_base, uint64_t ktext_size)
{
    /* Selector must be kernel code segment (0x0020) */
    uint16_t sel;
    memcpy(&sel, e + 2, 2);
    if (sel != 0x0020)
        return 0;

    /* Present bit must be set */
    if (!((e[5] >> 7) & 1))
        return 0;

    /* Type must be interrupt gate (14) or trap gate (15) */
    uint8_t type = e[5] & 0x0F;
    if (type != 14 && type != 15)
        return 0;

    /* Reserved bytes 12-15 must be zero */
    uint32_t reserved;
    memcpy(&reserved, e + 12, 4);
    if (reserved != 0)
        return 0;

    /* Reconstructed handler must point into kernel .text range */
    uint16_t off_low, off_mid;
    uint32_t off_high;
    memcpy(&off_low, e + 0, 2);
    memcpy(&off_mid, e + 6, 2);
    memcpy(&off_high, e + 8, 4);
    uint64_t handler = (uint64_t)off_low |
                       ((uint64_t)off_mid << 16) |
                       ((uint64_t)off_high << 32);

    if (handler < ktext_base || handler >= ktext_base + ktext_size)
        return 0;

    return 1;
}

/*
 * Scan kernel .data/.bss for the IDT by pattern-matching gate descriptors.
 * Returns 0 on success (idt_base_out is set), -1 on failure.
 *
 * Phase 1: Page-aligned scan (fast - IDT is almost certainly page-aligned).
 * Phase 2: 16-byte aligned scan (thorough fallback).
 */
#define IDT_SCAN_RANGE    0x4000000  /* 64MB: matches TSS scan range */
#define IDT_KTEXT_RANGE   0x2000000  /* 32MB: handler address validation */
#define IDT_QUICK_MIN     3          /* min valid of first 4 entries */
#define IDT_CONFIRM_MIN   16         /* min valid of first 20 entries */

static int
find_idt_base(int sock, uint64_t *idt_base_out)
{
    uint64_t kdata_base = (uint64_t)KERNEL_ADDRESS_DATA_BASE;
    uint64_t ktext_base = (uint64_t)KERNEL_ADDRESS_TEXT_BASE;
    uint64_t scan_end = kdata_base + IDT_SCAN_RANGE;
    uint8_t buf[4096];
    int chunks_scanned = 0;

    send_response(sock, "Scanning %luMB for IDT gate descriptors...\n",
                  (unsigned long)(IDT_SCAN_RANGE / (1024 * 1024)));

    /* Phase 1: Page-aligned scan (check offset 0 of each 4KB chunk) */
    send_response(sock, "Phase 1: page-aligned scan...\n");

    for (uint64_t addr = kdata_base; addr < scan_end; addr += 4096) {
        if (kernel_copyout(addr, buf, 4096) != 0) {
            chunks_scanned++;
            continue;
        }
        chunks_scanned++;

        if ((chunks_scanned & 0x7FF) == 0)
            send_response(sock, "  ...%d chunks (%luMB)\n",
                          chunks_scanned,
                          (unsigned long)chunks_scanned * 4096 / (1024 * 1024));

        /* Quick filter: check entries 0-3 at offset 0 */
        int valid = 0;
        for (int v = 0; v < 4; v++) {
            if (is_valid_idt_gate(buf + v * 16, ktext_base, IDT_KTEXT_RANGE))
                valid++;
        }
        if (valid < IDT_QUICK_MIN)
            continue;

        send_response(sock, "  candidate at 0x%lx (%d/4 quick match)\n",
                      addr, valid);

        /* Confirm: check entries 0-19 */
        int confirmed = 0;
        for (int v = 0; v < 20; v++) {
            if (is_valid_idt_gate(buf + v * 16, ktext_base, IDT_KTEXT_RANGE))
                confirmed++;
        }
        if (confirmed >= IDT_CONFIRM_MIN) {
            send_response(sock, "  CONFIRMED: IDT at 0x%lx (%d/20 valid)\n",
                          addr, confirmed);
            *idt_base_out = addr;
            return 0;
        }
        send_response(sock, "  rejected (%d/20, need %d)\n",
                      confirmed, IDT_CONFIRM_MIN);
    }

    send_response(sock, "Phase 1: not found (%d chunks)\n", chunks_scanned);

    /* Phase 2: 16-byte aligned scan (thorough) */
    send_response(sock, "Phase 2: 16-byte aligned scan...\n");
    chunks_scanned = 0;

    for (uint64_t addr = kdata_base; addr < scan_end; addr += 4096) {
        if (kernel_copyout(addr, buf, 4096) != 0) {
            chunks_scanned++;
            continue;
        }
        chunks_scanned++;

        if ((chunks_scanned & 0x7FF) == 0)
            send_response(sock, "  ...%d chunks (%luMB)\n",
                          chunks_scanned,
                          (unsigned long)chunks_scanned * 4096 / (1024 * 1024));

        for (int off = 16; off < 4096; off += 16) {
            /* Fast reject: check selector byte of first entry */
            if (buf[off + 2] != 0x20 || buf[off + 3] != 0x00)
                continue;

            /* Check entries 0-3 */
            int valid = 0;
            if (off + 64 <= 4096) {
                for (int v = 0; v < 4; v++) {
                    if (is_valid_idt_gate(buf + off + v * 16,
                                          ktext_base, IDT_KTEXT_RANGE))
                        valid++;
                }
            } else {
                /* Entries span chunk boundary - targeted read */
                uint8_t span[64];
                if (addr + off + 64 > scan_end)
                    continue;
                if (kernel_copyout(addr + off, span, 64) != 0)
                    continue;
                for (int v = 0; v < 4; v++) {
                    if (is_valid_idt_gate(span + v * 16,
                                          ktext_base, IDT_KTEXT_RANGE))
                        valid++;
                }
            }
            if (valid < IDT_QUICK_MIN)
                continue;

            /* Confirm: read entries 0-19 (320 bytes) */
            uint64_t cand = addr + off;
            uint8_t confirm_buf[320];
            send_response(sock, "  candidate at 0x%lx (off=0x%x, %d/4)\n",
                          cand, off, valid);

            if (cand + 320 > scan_end)
                continue;
            if (kernel_copyout(cand, confirm_buf, 320) != 0)
                continue;

            int confirmed = 0;
            for (int v = 0; v < 20; v++) {
                if (is_valid_idt_gate(confirm_buf + v * 16,
                                      ktext_base, IDT_KTEXT_RANGE))
                    confirmed++;
            }
            if (confirmed >= IDT_CONFIRM_MIN) {
                send_response(sock, "  CONFIRMED: IDT at 0x%lx (%d/20 valid)\n",
                              cand, confirmed);
                *idt_base_out = cand;
                return 0;
            }
            send_response(sock, "  rejected (%d/20, need %d)\n",
                          confirmed, IDT_CONFIRM_MIN);
        }
    }

    send_response(sock, "Phase 2: not found (%d chunks)\n", chunks_scanned);
    send_response(sock, "ERROR: Could not locate IDT in %luMB\n",
                  (unsigned long)(IDT_SCAN_RANGE / (1024 * 1024)));
    return -1;
}

#undef IDT_SCAN_RANGE
#undef IDT_KTEXT_RANGE
#undef IDT_QUICK_MIN
#undef IDT_CONFIRM_MIN

/*
 * idt_diag - Diagnostic scan to understand why IDT discovery fails.
 *
 * Scans 64MB from DATA_BASE with relaxed criteria (no selector or handler
 * range checks) to find any gate-descriptor-like patterns. Reports:
 *   - How many chunks are readable vs zero-filled
 *   - Total individual gate-like entries found (present + type 14/15 + reserved=0)
 *   - Candidate locations where 3+ consecutive entries match relaxed criteria
 *   - Selector values and handler addresses at each candidate
 *
 * This reveals whether the IDT uses a different selector, handlers point
 * outside the expected range, or the IDT is beyond the normal scan range.
 */
static void
cmd_idt_diag(int sock)
{
    uint64_t kdata_base = (uint64_t)KERNEL_ADDRESS_DATA_BASE;
    uint64_t ktext_base = (uint64_t)KERNEL_ADDRESS_TEXT_BASE;
    uint64_t scan_range = 0x4000000; /* 64MB */
    int total_chunks = scan_range / 4096;
    uint8_t buf[4096];

    send_response(sock, "=== IDT Diagnostic Scan ===\n");
    send_response(sock, "DATA_BASE: 0x%lx\n", kdata_base);
    send_response(sock, "TEXT_BASE: 0x%lx\n", ktext_base);
    send_response(sock, "Scan range: %luMB (%d chunks)\n\n",
                  (unsigned long)(scan_range / (1024 * 1024)), total_chunks);

    int readable_chunks = 0;
    int zero_chunks = 0;
    int total_gate_like = 0; /* individual entries matching relaxed criteria */

    /* Selector histogram: track most common selectors in gate-like entries */
    #define DIAG_SEL_HIST 16
    struct { uint16_t sel; int count; } sel_hist[DIAG_SEL_HIST];
    int num_sels = 0;

    /* Candidates: page-aligned locations with 3+ consecutive relaxed gates */
    #define MAX_DIAG_CANDIDATES 32
    struct {
        uint64_t addr;
        int relaxed_count;  /* of first 4 entries */
        int strict_count;   /* of first 4 entries (with sel=0x20 + handler check) */
        uint16_t selectors[4];
        uint64_t handlers[4];
        uint8_t types[4];
        uint8_t present[4];
    } cands[MAX_DIAG_CANDIDATES];
    int num_cands = 0;

    for (int chunk = 0; chunk < total_chunks; chunk++) {
        uint64_t addr = kdata_base + (uint64_t)chunk * 4096;

        if (chunk % 4096 == 0)
            send_response(sock, "  ...%d/%d chunks (%luMB)\n",
                          chunk, total_chunks,
                          (unsigned long)((uint64_t)chunk * 4096 / (1024 * 1024)));

        if (kernel_copyout(addr, buf, sizeof(buf)) != 0)
            continue;
        readable_chunks++;

        /* Check if first 64 bytes all zero (quick skip) */
        int all_zero = 1;
        for (int i = 0; i < 64; i++) {
            if (buf[i] != 0) { all_zero = 0; break; }
        }
        if (all_zero) { zero_chunks++; continue; }

        /* Check first 4 entries (page-aligned) with relaxed criteria */
        int relaxed = 0, strict = 0;
        uint16_t sels[4];
        uint64_t hdlrs[4];
        uint8_t types[4], pres[4];

        for (int e = 0; e < 4; e++) {
            uint8_t *entry = buf + e * 16;
            pres[e]  = (entry[5] >> 7) & 1;
            types[e] = entry[5] & 0x0F;

            uint32_t reserved;
            memcpy(&reserved, entry + 12, 4);
            memcpy(&sels[e], entry + 2, 2);

            uint16_t off_low, off_mid;
            uint32_t off_high;
            memcpy(&off_low, entry + 0, 2);
            memcpy(&off_mid, entry + 6, 2);
            memcpy(&off_high, entry + 8, 4);
            hdlrs[e] = (uint64_t)off_low |
                        ((uint64_t)off_mid << 16) |
                        ((uint64_t)off_high << 32);

            /* Relaxed: present=1, type=14|15, reserved=0 */
            if (pres[e] == 1 && (types[e] == 14 || types[e] == 15) &&
                reserved == 0) {
                relaxed++;
                total_gate_like++;

                /* Track selector in histogram */
                int found_sel = 0;
                for (int s = 0; s < num_sels; s++) {
                    if (sel_hist[s].sel == sels[e]) {
                        sel_hist[s].count++;
                        found_sel = 1;
                        break;
                    }
                }
                if (!found_sel && num_sels < DIAG_SEL_HIST) {
                    sel_hist[num_sels].sel = sels[e];
                    sel_hist[num_sels].count = 1;
                    num_sels++;
                }

                /* Strict: also sel=0x20 and handler in text range */
                if (sels[e] == 0x0020 &&
                    hdlrs[e] >= ktext_base &&
                    hdlrs[e] < ktext_base + 0x2000000)
                    strict++;
            }
        }

        if (relaxed >= 3 && num_cands < MAX_DIAG_CANDIDATES) {
            cands[num_cands].addr = addr;
            cands[num_cands].relaxed_count = relaxed;
            cands[num_cands].strict_count = strict;
            memcpy(cands[num_cands].selectors, sels, sizeof(sels));
            memcpy(cands[num_cands].handlers, hdlrs, sizeof(hdlrs));
            memcpy(cands[num_cands].types, types, sizeof(types));
            memcpy(cands[num_cands].present, pres, sizeof(pres));
            num_cands++;
        }

        /* Also scan all 256 entries in chunk for gate-like count */
        for (int e = 4; e < 256; e++) {
            uint8_t *entry = buf + e * 16;
            uint8_t p = (entry[5] >> 7) & 1;
            uint8_t t = entry[5] & 0x0F;
            uint32_t reserved;
            memcpy(&reserved, entry + 12, 4);
            if (p == 1 && (t == 14 || t == 15) && reserved == 0) {
                total_gate_like++;
                int found_sel = 0;
                uint16_t s;
                memcpy(&s, entry + 2, 2);
                for (int si = 0; si < num_sels; si++) {
                    if (sel_hist[si].sel == s) {
                        sel_hist[si].count++;
                        found_sel = 1;
                        break;
                    }
                }
                if (!found_sel && num_sels < DIAG_SEL_HIST) {
                    sel_hist[num_sels].sel = s;
                    sel_hist[num_sels].count = 1;
                    num_sels++;
                }
            }
        }
    }

    /* Report results */
    send_response(sock, "\n--- Scan Statistics ---\n");
    send_response(sock, "Total chunks: %d\n", total_chunks);
    send_response(sock, "Readable:     %d\n", readable_chunks);
    send_response(sock, "Zero-filled:  %d (first 64 bytes zero)\n", zero_chunks);
    send_response(sock, "Total gate-like entries (relaxed): %d\n\n", total_gate_like);

    /* Selector histogram */
    send_response(sock, "--- Selector Histogram ---\n");
    if (num_sels == 0) {
        send_response(sock, "  (no gate-like entries found at all)\n");
    } else {
        for (int i = 0; i < num_sels; i++)
            send_response(sock, "  sel=0x%04x : %d entries\n",
                          sel_hist[i].sel, sel_hist[i].count);
    }

    /* Candidates */
    send_response(sock, "\n--- Candidates (3+ relaxed matches at page boundary) ---\n");
    if (num_cands == 0) {
        send_response(sock, "  (none found)\n");
    } else {
        for (int i = 0; i < num_cands; i++) {
            send_response(sock, "\nCandidate %d: 0x%lx  (relaxed=%d strict=%d)\n",
                          i, cands[i].addr,
                          cands[i].relaxed_count, cands[i].strict_count);
            for (int e = 0; e < 4; e++) {
                send_response(sock,
                    "  [%d] p=%d type=%2d sel=0x%04x handler=0x%016lx",
                    e, cands[i].present[e], cands[i].types[e],
                    cands[i].selectors[e], cands[i].handlers[e]);
                if (cands[i].handlers[e] >= ktext_base &&
                    cands[i].handlers[e] < ktext_base + 0x4000000)
                    send_response(sock, " [ktext+0x%lx]",
                                  cands[i].handlers[e] - ktext_base);
                send_response(sock, "\n");
            }
        }
    }

    send_response(sock, "\nOK\n");
}

/*
 * dump_idt - Discover and parse the Interrupt Descriptor Table
 *
 * Finds the IDT by scanning .data/.bss for valid gate descriptor patterns,
 * reads all 256 gate descriptors, and displays handler addresses, IST
 * assignments, and gate types. Key output for singlestep primitive:
 * #DB (vec 1) and #GP (vec 13) handler addresses and IST indices.
 */
static void
cmd_dump_idt(int sock)
{
    intptr_t ktext_base = KERNEL_ADDRESS_TEXT_BASE;
    uint64_t text_start = (uint64_t)ktext_base;
    uint64_t text_end = text_start + 0x1000000;

    uint64_t idt_base = 0;
    int found_idt = 0;

    send_response(sock, "=== IDT Discovery ===\n\n");

    found_idt = (find_idt_base(sock, &idt_base) == 0);

    if (!found_idt) {
        send_response(sock, "OK\n");
        return;
    }

    /* Read full IDT: 256 entries × 16 bytes = 4096 bytes */
    uint8_t idt[4096];
    if (kernel_copyout(idt_base, idt, sizeof(idt)) != 0) {
        send_response(sock, "ERROR: Failed to read IDT at 0x%lx\n", idt_base);
        send_response(sock, "OK\n");
        return;
    }

    /* Vector name table */
    static const char *vec_name[256] = {
        [0]  = "#DE Divide",
        [1]  = "#DB Debug ***",
        [2]  = "NMI",
        [3]  = "#BP Breakpoint",
        [4]  = "#OF Overflow",
        [5]  = "#BR Bound",
        [6]  = "#UD InvalidOp",
        [7]  = "#NM NoMath",
        [8]  = "#DF DoubleFault",
        [9]  = "CoprocOverrun",
        [10] = "#TS InvalidTSS",
        [11] = "#NP SegNotPres",
        [12] = "#SS StackFault",
        [13] = "#GP GenProt ***",
        [14] = "#PF PageFault",
        [16] = "#MF x87FPU",
        [17] = "#AC AlignChk",
        [18] = "#MC MachineChk",
        [19] = "#XF SIMD",
        [0x80] = "Syscall"
    };

    send_response(sock, "\n--- IDT Entries ---\n");
    send_response(sock, "Vec  Name             Handler              Sel  IST Type DPL\n");
    send_response(sock, "---- ---------------- -------------------- ---- --- ---- ---\n");

    int text_count = 0, present_count = 0;
    int ist_vectors[8][16]; /* ist_vectors[ist][n] = vector numbers */
    int ist_counts[8] = {0};

    for (int v = 0; v < 256; v++) {
        uint8_t *e = idt + v * 16;

        uint16_t off_low, off_mid, sel;
        uint32_t off_high;
        memcpy(&off_low, e + 0, 2);
        memcpy(&sel, e + 2, 2);
        memcpy(&off_mid, e + 6, 2);
        memcpy(&off_high, e + 8, 4);

        uint8_t ist  = e[4] & 0x07;
        uint8_t type = e[5] & 0x0F;
        uint8_t dpl  = (e[5] >> 5) & 0x03;
        uint8_t p    = (e[5] >> 7) & 0x01;

        uint64_t handler = (uint64_t)off_low |
                           ((uint64_t)off_mid << 16) |
                           ((uint64_t)off_high << 32);

        if (p) present_count++;
        if (p && handler >= text_start && handler < text_end)
            text_count++;

        if (ist > 0 && ist < 8 && ist_counts[ist] < 16)
            ist_vectors[ist][ist_counts[ist]++] = v;

        /* Show: first 20 vectors, syscall, anything with IST, or *** vectors */
        int show = (v < 20) || (v == 0x80) || (ist > 0 && p);
        if (!show) continue;

        const char *name = vec_name[v] ? vec_name[v] : "";
        const char *tname = (type == 14) ? "IntG" :
                            (type == 15) ? "TrpG" : "????";

        if (!p) {
            send_response(sock, "%3d  %-16s (not present)\n", v, name);
        } else if (handler >= text_start && handler < text_end) {
            send_response(sock, "%3d  %-16s ktext+0x%-12lx 0x%02x  %d  %s  %d\n",
                          v, name, handler - text_start, sel, ist, tname, dpl);
        } else {
            send_response(sock, "%3d  %-16s 0x%016lx 0x%02x  %d  %s  %d\n",
                          v, name, handler, sel, ist, tname, dpl);
        }
    }

    /* Summary */
    send_response(sock, "\n--- Summary ---\n");
    send_response(sock, "IDT base: 0x%lx\n", idt_base);
    send_response(sock, "Present: %d/256    .text handlers: %d\n",
                  present_count, text_count);

    /* IST assignments */
    send_response(sock, "\n--- IST Assignments ---\n");
    int any_ist = 0;
    for (int i = 1; i < 8; i++) {
        if (ist_counts[i] > 0) {
            any_ist = 1;
            send_response(sock, "  IST%d: ", i);
            for (int j = 0; j < ist_counts[i]; j++) {
                if (j > 0) send_response(sock, ", ");
                send_response(sock, "vec %d", ist_vectors[i][j]);
                if (vec_name[ist_vectors[i][j]])
                    send_response(sock, " (%s)", vec_name[ist_vectors[i][j]]);
            }
            send_response(sock, "\n");
        }
    }
    if (!any_ist)
        send_response(sock, "  (no IST assignments found)\n");

    /* Key vectors for singlestep primitive */
    send_response(sock, "\n--- Singlestep Prerequisites ---\n");

    for (int vec = 0; vec < 2; vec++) {
        int v = (vec == 0) ? 1 : 13; /* #DB, #GP */
        uint8_t *e = idt + v * 16;
        uint16_t ol, om;
        uint32_t oh;
        memcpy(&ol, e + 0, 2);
        memcpy(&om, e + 6, 2);
        memcpy(&oh, e + 8, 4);
        uint64_t h = (uint64_t)ol | ((uint64_t)om << 16) | ((uint64_t)oh << 32);
        uint8_t ist = e[4] & 0x07;
        const char *label = (v == 1) ? "#DB (debug/singlestep)" : "#GP (for doreti_iret finder)";

        send_response(sock, "  Vec %2d %-26s handler=", v, label);
        if (h >= text_start && h < text_end)
            send_response(sock, "ktext+0x%lx", h - text_start);
        else
            send_response(sock, "0x%lx", h);
        send_response(sock, "  IST=%d\n", ist);
    }

    send_response(sock, "\nNotes:\n");
    send_response(sock, "  IST=0 means handler uses current kernel stack (need TSS mod for controlled stack)\n");
    send_response(sock, "  IST>0 means handler uses dedicated IST stack from TSS (can read/overwrite via kR/W)\n");
    send_response(sock, "  IDT base address is needed for Phase 7c (redirect #DB handler)\n");
    send_response(sock, "OK\n");
}

/*
 * Step 7 helpers: #GP trap frame method (sleirsgoevy's technique)
 *
 * Trigger iretq to fault by returning to a non-canonical RIP,
 * intercept the #GP via IST stack manipulation, and read doreti_iret
 * from the signal context's mc_rip.
 */

/* Signal handler for #GP trap frame method (catches SIGBUS and SIGSEGV) */
static void
gp_trap_fault_handler(int sig, siginfo_t *info, void *ctx)
{
    (void)info;
    ucontext_t *uc = (ucontext_t *)ctx;
    gp_trap_doreti_addr = uc->uc_mcontext.mc_rip;
    gp_trap_mc_cs       = uc->uc_mcontext.mc_cs;
    gp_trap_mc_err      = uc->uc_mcontext.mc_err;
    gp_trap_sig_received = sig;
    gp_trap_got_result  = 1;
    siglongjmp(gp_trap_jmp_env, 1);
}

/* Writer thread: continuously overwrites CS field on IST page */
static int
gp_trap_writer_fn(void *arg)
{
    volatile uint8_t *ist_page = (volatile uint8_t *)arg;
    /*
     * IST stack trap frame layout (top at page+0x1000):
     *   page+0xFF8: SS        (IST top - 0x08)
     *   page+0xFF0: RSP       (IST top - 0x10)
     *   page+0xFE8: RFLAGS    (IST top - 0x18)  <- writer sets 0x202
     *   page+0xFE0: CS        (IST top - 0x20)   <- writer sets 0x43
     *   page+0xFD8: RIP       (IST top - 0x28)   <- doreti_iret address
     *   page+0xFD0: Error code(IST top - 0x30)
     */
    volatile uint64_t *p_cs     = (volatile uint64_t *)(ist_page + 0xFE0);
    volatile uint64_t *p_rflags = (volatile uint64_t *)(ist_page + 0xFE8);

    while (!gp_trap_stop_writer) {
        *p_cs     = 0x43;   /* user-mode CS selector */
        *p_rflags = 0x202;  /* IF set, reserved bit 1 set */
    }
    return 0;
}

/*
 * find_tss_in_kdata - Scan kernel .data for TSS structures.
 *
 * The x86-64 TSS (Task State Segment) is 104 bytes.  FreeBSD allocates
 * one per CPU in a contiguous array.  We pattern-match:
 *   - rsvd0 (offset 0) == 0
 *   - rsp0 is a kernel address
 *   - rsp1, rsp2 == 0 (FreeBSD doesn't use ring 1/2)
 *   - reserved field at offset 0x64 == 0
 *   - IST fields are 0 or kernel addresses
 *   - A second TSS follows 104+ bytes later (per-CPU array)
 *
 * Returns the kernel VA of the first TSS, or 0 on failure.
 * If stride_out is non-NULL, stores the per-CPU TSS stride.
 */
static uint64_t
find_tss_in_kdata(int sock, int *stride_out)
{
    uint64_t kdata_base = (uint64_t)KERNEL_ADDRESS_DATA_BASE;
    uint64_t ktext_base = (uint64_t)KERNEL_ADDRESS_TEXT_BASE;
    uint64_t scan_size  = 0x4000000; /* 64MB */
    uint8_t buf[4096];

    send_response(sock, "Scanning 64MB from kdata for TSS...\n");

    for (uint64_t off = 0; off < scan_size; off += sizeof(buf)) {
        if (kernel_copyout(kdata_base + off, buf, sizeof(buf)) != 0)
            continue;

        /* TSS is 104 bytes; scan at 16-byte alignment */
        for (int i = 0; i <= (int)sizeof(buf) - 104; i += 16) {
            uint32_t rsvd0;
            uint64_t rsp0, rsp1, rsp2;

            memcpy(&rsvd0, buf + i, 4);
            if (rsvd0 != 0)
                continue;

            memcpy(&rsp0, buf + i + 4, 8);
            /* rsp0 must be a kernel address */
            if (rsp0 < (uint64_t)ktext_base || rsp0 == 0)
                continue;

            memcpy(&rsp1, buf + i + 12, 8);
            memcpy(&rsp2, buf + i + 20, 8);
            if (rsp1 != 0 || rsp2 != 0)
                continue;

            /* Check reserved field at offset 0x64 */
            uint32_t rsvd64;
            memcpy(&rsvd64, buf + i + 0x64, 4);
            if (rsvd64 != 0)
                continue;

            /* Validate IST1-7 (offsets 0x24..0x5b): each 0 or kernel addr */
            int ist_ok = 1;
            for (int ist = 0; ist < 7; ist++) {
                uint64_t ist_val;
                memcpy(&ist_val, buf + i + 0x24 + ist * 8, 8);
                if (ist_val != 0 &&
                    ist_val < (uint64_t)ktext_base) {
                    ist_ok = 0;
                    break;
                }
            }
            if (!ist_ok)
                continue;

            /* Confirm: look for a second TSS at +104 or further (per-CPU) */
            uint64_t tss_va = kdata_base + off + i;
            int found_second = 0;

            /* TSS entries might be 104 bytes apart, or padded to 128/256 */
            for (int stride = 104; stride <= 4096; stride += 8) {
                uint64_t next_addr = tss_va + stride;
                uint32_t next_rsvd0;
                uint64_t next_rsp0;

                if (kernel_copyout(next_addr, &next_rsvd0, 4) != 0)
                    continue;
                if (next_rsvd0 != 0)
                    continue;
                if (kernel_copyout(next_addr + 4, &next_rsp0, 8) != 0)
                    continue;
                if (next_rsp0 >= (uint64_t)ktext_base && next_rsp0 != 0) {
                    found_second = 1;
                    if (stride_out)
                        *stride_out = stride;
                    send_response(sock, "TSS found at 0x%lx (stride=%d to next)\n",
                                  tss_va, stride);
                    break;
                }
            }

            if (found_second)
                return tss_va;
        }
    }

    return 0;
}

/*
 * find_user_page_pa - Find the physical address of a user page.
 *
 * Write a magic value to an mmap'd page, then:
 *   1. kernel_get_proc(getpid()) -> read vmspace at proc + VMSPACE_OFFSET
 *   2. Scan vmspace (1024 bytes) for page-aligned values < 32GB
 *   3. Try each as CR3 with vaddr_to_paddr_quiet()
 *   4. Verify by reading the magic value back via DMAP
 *
 * Returns the physical address of the page, or 0 on failure.
 */
static uint64_t
find_user_page_pa(int sock, uint64_t dmap_base, void *user_page)
{
    volatile uint64_t *magic = (volatile uint64_t *)user_page;
    *magic = 0xDEAD1337CAFE4242ULL;

    intptr_t proc = kernel_get_proc(getpid());
    if (proc == 0) {
        send_response(sock, "  kernel_get_proc failed\n");
        return 0;
    }

    /* Read vmspace pointer from proc + KERNEL_OFFSET_PROC_P_VMSPACE */
    uint64_t vmspace = kernel_getlong(proc + KERNEL_OFFSET_PROC_P_VMSPACE);
    if (vmspace == 0) {
        send_response(sock, "  vmspace is NULL\n");
        return 0;
    }

    send_response(sock, "  proc=0x%lx vmspace=0x%lx\n", (uint64_t)proc, vmspace);

    /* Scan vmspace for plausible CR3 values (page-aligned, < 32GB) */
    uint8_t vsbuf[1024];
    if (kernel_copyout(vmspace, vsbuf, sizeof(vsbuf)) != 0) {
        send_response(sock, "  failed to read vmspace\n");
        return 0;
    }

    uint64_t page_va = (uint64_t)user_page;

    for (int off = 0; off <= (int)sizeof(vsbuf) - 8; off += 8) {
        uint64_t cr3_cand;
        memcpy(&cr3_cand, vsbuf + off, 8);

        /* Must be page-aligned, nonzero, < 32GB */
        if (cr3_cand == 0 || (cr3_cand & 0xFFF) != 0)
            continue;
        if (cr3_cand >= 0x800000000ULL) /* 32GB */
            continue;

        uint64_t pa, flags;
        if (vaddr_to_paddr_quiet(dmap_base, cr3_cand, page_va,
                                 &pa, &flags) != 0)
            continue;

        /* Verify: read magic back via DMAP */
        uint64_t readback;
        if (kernel_copyout(dmap_base + pa, &readback, 8) != 0)
            continue;

        if (readback == 0xDEAD1337CAFE4242ULL) {
            send_response(sock, "  user page PA=0x%lx (CR3 cand at vmspace+0x%x)\n",
                          pa, off);
            return pa;
        }
    }

    send_response(sock, "  could not find user page PA\n");
    return 0;
}

/*
 * find_doreti_iret - Phase 7b: Locate doreti_iret gadget in kernel .text
 *
 * In FreeBSD the interrupt return path goes through doreti -> doreti_iret
 * where iretq executes to return from interrupt/exception context.
 * The #GP handler references this address for fault-on-iret detection.
 *
 * This command:
 *   1. Discovers IDT and extracts key handler addresses (#DB, #DF, #GP)
 *   2. Walks page tables to get handler physical addresses
 *   3. Scans DMAP-accessible physical pages around handlers for iretq
 *   4. Broader scan of kernel .text physical region
 *   5. Classifies candidates by proximity to #GP and swapgs presence
 */
static void
cmd_find_doreti_iret(int sock, const char *arg)
{
    intptr_t ktext_base = KERNEL_ADDRESS_TEXT_BASE;
    uint64_t pm_cr3 = get_kernel_cr3();
    uint64_t dmap_base = get_dmap_base();

    send_response(sock, "=== Phase 7b: doreti_iret Finder ===\n\n");

    /* If user provided a known ktext offset, use it directly */
    if (arg && *arg) {
        uint64_t offset = strtoull(arg, NULL, 16);
        if (offset > 0 && offset < 0x2000000) {
            uint64_t va = (uint64_t)ktext_base + offset;
            send_response(sock, "Using provided offset: ktext+0x%lx\n", offset);
            send_response(sock, "\n*** doreti_iret = 0x%lx (ktext+0x%lx) ***\n", va, offset);
            send_response(sock, "Confidence: USER-PROVIDED\n");
            send_response(sock, "\nNotes:\n");
            send_response(sock, "  Phase 7c will redirect #DB to singlestep "
                          "through this instruction\n");
            send_response(sock, "OK\n");
            return;
        }
        send_response(sock, "WARNING: invalid offset '%s', proceeding with scan\n\n", arg);
    }

    /* Byte signatures */
    static const uint8_t sig_iretq[]  = {0x48, 0xcf};
    static const uint8_t sig_swapgs[] = {0x0f, 0x01, 0xf8};

    /* Candidate storage */
    #define MAX_DORETI_CANDIDATES 64
    struct doreti_candidate {
        uint64_t paddr;
        uint64_t ktext_offset;
        int has_swapgs_before;
        int near_handler;       /* vec number, or 0 for broad scan */
        int page_dist;
    } candidates[MAX_DORETI_CANDIDATES];
    int num_candidates = 0;

    /* Key handler info */
    struct {
        int vec;
        const char *name;
        uint64_t handler_va;
        uint8_t ist;
        uint64_t handler_pa;
        int pa_valid;
        int dmap_readable;
    } key_handlers[3] = {
        { 1,  "#DB Debug",       0, 0, 0, 0, 0},
        { 8,  "#DF DoubleFault", 0, 0, 0, 0, 0},
        {13,  "#GP GenProt",     0, 0, 0, 0, 0},
    };

    /* ---- Step 0: Symbol Table Lookup ---- */
    /*
     * Search .data for the ELF string "doreti_iret", then locate the
     * corresponding Elf64_Sym entry to read the symbol's virtual address.
     * This bypasses XOM entirely - no .text reads needed.
     */
    send_response(sock, "--- Step 0: Symbol Table Lookup ---\n");
    {
        uint64_t data_start = (uint64_t)KERNEL_ADDRESS_DATA_BASE;
        uint64_t data_size  = 0x8000000; /* 128MB - covers .data + .bss + metadata */
        uint8_t sbuf[4096];
        uint64_t string_addr = 0;

        send_response(sock, "Searching 128MB for 'doreti_iret' string...\n");

        /* Part A: Find "\0doreti_iret\0" in .data (strtab entry) */
        for (uint64_t addr = data_start;
             addr < data_start + data_size && !string_addr;
             addr += sizeof(sbuf)) {
            int chunk = (int)((addr - data_start) / sizeof(sbuf));
            if (chunk % 8192 == 0)
                send_response(sock, "  ...%luMB\n",
                              (unsigned long)((addr - data_start) / (1024 * 1024)));
            if (kernel_copyout(addr, sbuf, sizeof(sbuf)) != 0)
                continue;

            for (int i = 1; i <= (int)sizeof(sbuf) - 12; i++) {
                if (sbuf[i] != 'd')
                    continue;
                if (memcmp(sbuf + i, "doreti_iret", 11) != 0)
                    continue;
                /* Check null before and after */
                if (sbuf[i - 1] != 0)
                    continue;
                if (i + 11 < (int)sizeof(sbuf) && sbuf[i + 11] != 0)
                    continue;
                string_addr = addr + i;
                break;
            }
        }

        if (string_addr) {
            send_response(sock, "Found 'doreti_iret' at 0x%lx (kdata+0x%lx)\n",
                          string_addr, string_addr - data_start);

            /* Check for "doreti_iret_fault" right after (strtab adjacency) */
            int have_fault_str = 0;
            uint8_t after[20];
            if (kernel_copyout(string_addr + 12, after, 18) == 0) {
                if (memcmp(after, "doreti_iret_fault", 17) == 0)
                    have_fault_str = 1;
            }
            if (have_fault_str)
                send_response(sock, "  'doreti_iret_fault' adjacent in strtab [good]\n");

            /* Part B: Find Elf64_Sym entry for this string.
             *   Elf64_Sym (24 bytes):
             *     [0..3]   st_name  (uint32 - offset into strtab)
             *     [4]      st_info  [5] st_other  [6..7] st_shndx
             *     [8..15]  st_value (uint64 - symbol address)
             *     [16..23] st_size  (uint64)
             */
            send_response(sock, "Searching for Elf64_Sym entry...\n");

            uint64_t doreti_va = 0;
            uint64_t doreti_fault_va = 0;
            int sym_candidates = 0;

            for (uint64_t addr = data_start;
                 addr < data_start + data_size;
                 addr += sizeof(sbuf)) {
                if (doreti_va && have_fault_str)
                    break; /* found with strong verification */
                if (kernel_copyout(addr, sbuf, sizeof(sbuf)) != 0)
                    continue;

                for (int i = 0; i <= (int)sizeof(sbuf) - 24; i += 8) {
                    uint32_t st_name;
                    uint8_t  st_other;
                    uint16_t st_shndx;
                    uint64_t st_value, st_size;

                    memcpy(&st_value, sbuf + i + 8, 8);

                    /* Quick filter: st_value must be in ktext range */
                    if (st_value < (uint64_t)ktext_base ||
                        st_value >= (uint64_t)ktext_base + 0x2000000)
                        continue;

                    memcpy(&st_name, sbuf + i, 4);
                    st_other = sbuf[i + 5];
                    memcpy(&st_shndx, sbuf + i + 6, 2);
                    memcpy(&st_size, sbuf + i + 16, 8);

                    /* Validate Elf64_Sym fields */
                    if (st_name == 0 || st_name > 0x1000000)
                        continue;
                    if (st_other != 0 && st_other != 2)
                        continue;
                    if (st_shndx == 0 || st_shndx >= 0xff00)
                        continue;
                    if (st_size > 0x1000)
                        continue;

                    /* Compute strtab_base = string_addr - st_name */
                    uint64_t strtab_base = string_addr - (uint64_t)st_name;
                    if (strtab_base < data_start ||
                        strtab_base >= data_start + data_size)
                        continue;

                    /* Verify: strtab[0] must be '\0' */
                    uint8_t first;
                    if (kernel_copyout(strtab_base, &first, 1) != 0 ||
                        first != 0)
                        continue;

                    sym_candidates++;
                    send_response(sock,
                        "  sym: st_name=%u st_value=0x%lx (ktext+0x%lx) "
                        "st_size=%lu strtab=0x%lx\n",
                        st_name, st_value,
                        st_value - (uint64_t)ktext_base,
                        (unsigned long)st_size, strtab_base);

                    doreti_va = st_value;

                    /* If doreti_iret_fault string is adjacent, find its sym too */
                    if (have_fault_str && !doreti_fault_va) {
                        /* doreti_iret_fault string is at string_addr+12 */
                        uint32_t fault_st_name = st_name + 12;
                        /* Search nearby in symtab for this entry */
                        int search_start = (i >= 240) ? i - 240 : 0;
                        int search_end = (i + 264 <= (int)sizeof(sbuf) - 24) ?
                                         i + 264 : (int)sizeof(sbuf) - 24;
                        for (int j = search_start; j <= search_end; j += 8) {
                            if (j == i) continue;
                            uint32_t fn;
                            uint64_t fv;
                            memcpy(&fn, sbuf + j, 4);
                            memcpy(&fv, sbuf + j + 8, 8);
                            if (fn == fault_st_name &&
                                fv >= (uint64_t)ktext_base &&
                                fv < (uint64_t)ktext_base + 0x2000000) {
                                doreti_fault_va = fv;
                                send_response(sock,
                                    "  doreti_iret_fault: 0x%lx (ktext+0x%lx)\n",
                                    fv, fv - (uint64_t)ktext_base);
                                break;
                            }
                        }
                    }

                    if (have_fault_str && doreti_fault_va)
                        break; /* high confidence */
                }
            }

            if (doreti_va) {
                send_response(sock, "\n*** doreti_iret = 0x%lx (ktext+0x%lx) ***\n",
                              doreti_va, doreti_va - (uint64_t)ktext_base);
                if (doreti_fault_va)
                    send_response(sock,
                        "*** doreti_iret_fault = 0x%lx (ktext+0x%lx) ***\n",
                        doreti_fault_va,
                        doreti_fault_va - (uint64_t)ktext_base);
                send_response(sock, "Confidence: %s\n",
                              (have_fault_str && doreti_fault_va) ? "HIGH" :
                              have_fault_str ? "MEDIUM" : "LOW");

                send_response(sock, "\nNotes:\n");
                send_response(sock, "  Address found via ELF symbol table in .data\n");
                send_response(sock, "  Phase 7c will redirect #DB to singlestep "
                              "through this instruction\n");
                send_response(sock, "OK\n");
                return; /* success - skip all other steps */
            }

            send_response(sock, "Symbol entry not found (%d candidates examined)\n",
                          sym_candidates);
        } else {
            send_response(sock, "'doreti_iret' string not found in 128MB\n");
            send_response(sock, "Kernel appears stripped (no symbol table).\n");
            send_response(sock, "TIP: use 'find_doreti_iret <ktext_offset_hex>' with "
                          "a known offset from your firmware's offset database.\n");
        }

        send_response(sock, "Falling through to scan-based approach...\n\n");
    }

    /* ---- Step 1: IDT Discovery (gate descriptor pattern scan) ---- */
    send_response(sock, "--- Step 1: IDT Discovery ---\n");

    uint64_t idt_base = 0;
    uint64_t idt_access = 0; /* address for kernel read/write (may differ from idt_base if DMAP) */
    int found_idt = 0;

    if (find_idt_base(sock, &idt_base) == 0) {
        found_idt = 1;
        idt_access = idt_base; /* in .data — directly accessible */
        send_response(sock, "IDT base: 0x%lx\n", idt_base);
    } else {
        send_response(sock, "IDT not found (HV-managed?) - skipping to broad scan\n");
    }

    /* Read full IDT (if found) */
    uint8_t idt[4096];
    if (found_idt) {
        if (kernel_copyout(idt_base, idt, sizeof(idt)) != 0) {
            send_response(sock, "WARNING: Failed to read IDT at 0x%lx\n", idt_base);
            found_idt = 0;
        }
    }

    int vicinity_pages_readable = 0, vicinity_pages_blocked = 0;
    uint8_t page_buf[4096];

    if (found_idt) {
        /* ---- Step 2: Extract Key Handler Addresses ---- */
        send_response(sock, "\n--- Step 2: Key Handler Addresses ---\n");
        send_response(sock, "%-4s %-16s %-22s %s\n", "Vec", "Name", "Handler", "IST");
        send_response(sock, "---- ---------------- ---------------------- ---\n");

        for (int h = 0; h < 3; h++) {
            int v = key_handlers[h].vec;
            uint8_t *e = idt + v * 16;

            uint16_t off_low, off_mid;
            uint32_t off_high;
            memcpy(&off_low, e + 0, 2);
            memcpy(&off_mid, e + 6, 2);
            memcpy(&off_high, e + 8, 4);

            uint64_t handler = (uint64_t)off_low |
                               ((uint64_t)off_mid << 16) |
                               ((uint64_t)off_high << 32);
            uint8_t ist = e[4] & 0x07;
            uint8_t p = (e[5] >> 7) & 0x01;

            key_handlers[h].handler_va = handler;
            key_handlers[h].ist = ist;

            if (!p) {
                send_response(sock, "%3d  %-16s (not present)\n", v, key_handlers[h].name);
                continue;
            }

            if (handler >= (uint64_t)ktext_base &&
                handler < (uint64_t)ktext_base + 0x1000000) {
                send_response(sock, "%3d  %-16s ktext+0x%-14lx %d\n",
                              v, key_handlers[h].name,
                              handler - (uint64_t)ktext_base, ist);
            } else {
                send_response(sock, "%3d  %-16s 0x%-20lx %d\n",
                              v, key_handlers[h].name, handler, ist);
            }
        }

        /* ---- Step 3: Get Physical Addresses ---- */
        send_response(sock, "\n--- Step 3: Handler Physical Addresses ---\n");
        send_response(sock, "%-4s %-20s %-18s %s\n",
                      "Vec", "Handler VA", "Physical Addr", "DMAP");
        send_response(sock, "---- -------------------- ------------------ --------\n");

        for (int h = 0; h < 3; h++) {
            if (key_handlers[h].handler_va == 0)
                continue;

            uint64_t paddr, flags;
            if (vaddr_to_paddr_quiet(dmap_base, pm_cr3,
                                     key_handlers[h].handler_va,
                                     &paddr, &flags) == 0) {
                key_handlers[h].handler_pa = paddr;
                key_handlers[h].pa_valid = 1;

                /* Test DMAP readability */
                uint8_t test[8];
                if (kernel_copyout(dmap_base + paddr, test, sizeof(test)) == 0) {
                    key_handlers[h].dmap_readable = 1;
                    send_response(sock, "%3d  0x%016lx   0x%014lx   READABLE\n",
                                  key_handlers[h].vec,
                                  key_handlers[h].handler_va, paddr);
                } else {
                    send_response(sock, "%3d  0x%016lx   0x%014lx   BLOCKED\n",
                                  key_handlers[h].vec,
                                  key_handlers[h].handler_va, paddr);
                }
            } else {
                send_response(sock, "%3d  0x%016lx   TRANSLATION FAILED\n",
                              key_handlers[h].vec,
                              key_handlers[h].handler_va);
            }
        }

        /* ---- Step 4: Scan Handler Vicinity ---- */
        send_response(sock, "\n--- Step 4: Scanning Handler Vicinity (+-32KB) ---\n");

        for (int h = 0; h < 3; h++) {
            if (!key_handlers[h].pa_valid || !key_handlers[h].dmap_readable)
                continue;

            uint64_t base_pa = key_handlers[h].handler_pa & ~0xFFFUL;
            uint64_t scan_start = (base_pa > 8 * 0x1000) ? base_pa - 8 * 0x1000 : 0;
            uint64_t scan_end = base_pa + 8 * 0x1000;

            send_response(sock, "Scanning around vec %d %s (PA 0x%lx)...\n",
                          key_handlers[h].vec, key_handlers[h].name, base_pa);

            for (uint64_t pa = scan_start; pa < scan_end; pa += 0x1000) {
                if (kernel_copyout(dmap_base + pa, page_buf, sizeof(page_buf)) != 0) {
                    vicinity_pages_blocked++;
                    continue;
                }
                vicinity_pages_readable++;

                for (size_t i = 0; i < sizeof(page_buf) - 1; i++) {
                    if (memcmp(&page_buf[i], sig_iretq, sizeof(sig_iretq)) != 0)
                        continue;

                    if (num_candidates >= MAX_DORETI_CANDIDATES)
                        goto vicinity_done;

                    int has_swapgs = 0;
                    size_t check_start = (i >= 32) ? i - 32 : 0;
                    for (size_t j = check_start; j + 2 < i; j++) {
                        if (memcmp(&page_buf[j], sig_swapgs, sizeof(sig_swapgs)) == 0) {
                            has_swapgs = 1;
                            break;
                        }
                    }

                    uint64_t cand_pa = pa + i;
                    uint64_t est_ktext_off = (key_handlers[h].handler_va -
                                              (uint64_t)ktext_base) +
                                             (int64_t)(cand_pa - key_handlers[h].handler_pa);
                    int page_dist = (int)((int64_t)(pa - base_pa) / 0x1000);

                    candidates[num_candidates].paddr = cand_pa;
                    candidates[num_candidates].ktext_offset = est_ktext_off;
                    candidates[num_candidates].has_swapgs_before = has_swapgs;
                    candidates[num_candidates].near_handler = key_handlers[h].vec;
                    candidates[num_candidates].page_dist = page_dist;
                    num_candidates++;

                    send_response(sock, "  iretq @ PA 0x%lx (est ktext+0x%lx) swapgs=%s\n",
                                  cand_pa, est_ktext_off,
                                  has_swapgs ? "YES" : "NO");
                }
            }
        }
    vicinity_done:

        send_response(sock, "Handler vicinity: %d candidates, %d pages readable, %d blocked\n",
                      num_candidates, vicinity_pages_readable, vicinity_pages_blocked);
    } else {
        send_response(sock, "\n--- Steps 2-4: Skipped (no IDT) ---\n");
    }

    /* ---- Step 5: Broad Kernel .text Physical Scan ---- */
    send_response(sock, "\n--- Step 5: Broad Kernel .text Physical Scan ---\n");

    int broad_new = 0;
    int broad_readable = 0, broad_blocked = 0;

    /* Try to determine .text physical address range */
    uint64_t text_pa = 0;
    uint64_t text_flags;
    int have_text_pa = (vaddr_to_paddr_quiet(dmap_base, pm_cr3,
                        (uint64_t)ktext_base, &text_pa, &text_flags) == 0);

    /* Determine scan range */
    uint64_t broad_start, broad_end;
    if (have_text_pa) {
        send_response(sock, "ktext PA: 0x%lx (from page table walk)\n", text_pa);
        broad_start = (text_pa & ~0xFFFUL);
        /* Without IDT we have no handler seeds, scan wider */
        if (found_idt)
            broad_end = broad_start + 0x400000; /* 4MB */
        else
            broad_end = broad_start + 0x2000000; /* 32MB */
    } else {
        /* Use handler PA as anchor, scan wider range */
        send_response(sock, "ktext PA translation failed, using handler PA as anchor\n");
        uint64_t anchor = 0;
        for (int h = 0; h < 3; h++) {
            if (key_handlers[h].pa_valid) {
                anchor = key_handlers[h].handler_pa;
                break;
            }
        }
        if (anchor == 0) {
            send_response(sock, "No anchor PA available, skipping broad scan\n");
            goto classify;
        }
        broad_start = (anchor > 0x400000) ? (anchor & ~0xFFFUL) - 0x400000 : 0;
        broad_end = (anchor & ~0xFFFUL) + 0x400000;
    }

    /* Cap: 8192 pages (32MB) without IDT, 2048 (8MB) with */
    uint64_t max_pages = found_idt ? 2048 : 8192;
    if ((broad_end - broad_start) / 0x1000 > max_pages)
        broad_end = broad_start + max_pages * 0x1000;

    send_response(sock, "Scan range: PA 0x%lx - 0x%lx (%lu pages)\n",
                  broad_start, broad_end,
                  (broad_end - broad_start) / 0x1000);

    for (uint64_t pa = broad_start;
         pa < broad_end && num_candidates < MAX_DORETI_CANDIDATES;
         pa += 0x1000) {

        int page_num = (int)((pa - broad_start) / 0x1000);
        if (page_num % 1024 == 0)
            send_response(sock, "  ...%d pages (%luMB)\n",
                          page_num,
                          (unsigned long)(page_num * 4096 / (1024 * 1024)));

        if (kernel_copyout(dmap_base + pa, page_buf, sizeof(page_buf)) != 0) {
            broad_blocked++;
            continue;
        }
        broad_readable++;

        for (size_t i = 0; i < sizeof(page_buf) - 1; i++) {
            if (memcmp(&page_buf[i], sig_iretq, sizeof(sig_iretq)) != 0)
                continue;

            uint64_t cand_pa = pa + i;

            /* Skip if already found in handler vicinity scan */
            int already_found = 0;
            for (int c = 0; c < num_candidates - broad_new; c++) {
                if (candidates[c].paddr == cand_pa) {
                    already_found = 1;
                    break;
                }
            }
            if (already_found)
                continue;

            if (num_candidates >= MAX_DORETI_CANDIDATES)
                goto broad_done;

            /* Check for swapgs within 32 bytes before */
            int has_swapgs = 0;
            size_t check_start = (i >= 32) ? i - 32 : 0;
            for (size_t j = check_start; j + 2 < i; j++) {
                if (memcmp(&page_buf[j], sig_swapgs, sizeof(sig_swapgs)) == 0) {
                    has_swapgs = 1;
                    break;
                }
            }

            /* Estimate ktext offset using text_pa if available */
            uint64_t est_ktext_off;
            if (have_text_pa) {
                est_ktext_off = cand_pa - text_pa;
            } else {
                /* Estimate from nearest handler */
                est_ktext_off = 0;
                for (int h = 0; h < 3; h++) {
                    if (key_handlers[h].pa_valid) {
                        est_ktext_off = (key_handlers[h].handler_va -
                                         (uint64_t)ktext_base) +
                                        (int64_t)(cand_pa - key_handlers[h].handler_pa);
                        break;
                    }
                }
            }

            /* Determine nearest handler */
            int nearest = 0;
            int nearest_dist = 0x7FFFFFFF;
            for (int h = 0; h < 3; h++) {
                if (!key_handlers[h].pa_valid)
                    continue;
                int64_t d = (int64_t)(cand_pa - key_handlers[h].handler_pa);
                int dist_pages = (int)(d / 0x1000);
                if (dist_pages < 0) dist_pages = -dist_pages;
                if (dist_pages < nearest_dist) {
                    nearest_dist = dist_pages;
                    nearest = key_handlers[h].vec;
                }
            }

            candidates[num_candidates].paddr = cand_pa;
            candidates[num_candidates].ktext_offset = est_ktext_off;
            candidates[num_candidates].has_swapgs_before = has_swapgs;
            candidates[num_candidates].near_handler = (nearest_dist <= 16) ? nearest : 0;
            candidates[num_candidates].page_dist = nearest_dist;
            num_candidates++;
            broad_new++;

            if (has_swapgs) {
                send_response(sock, "  iretq @ PA 0x%lx (est ktext+0x%lx) swapgs=YES [new]\n",
                              cand_pa, est_ktext_off);
            }
        }
    }
broad_done:

    send_response(sock, "Broad scan: %d new candidates, %d pages readable, %d blocked\n",
                  broad_new, broad_readable, broad_blocked);

    /* ---- Step 5b: .data Pointer Scan for doreti_iret ---- */
    /*
     * If most .text pages are XOM-blocked via DMAP, the real doreti_iret
     * is unreachable by direct byte scan.  Alternative: scan .data for
     * pointers into early .text (first 1MB) where interrupt/trap handling
     * assembly lives.  FreeBSD's trap() compares tf_rip against
     * doreti_iret, so its address must be stored/referenced somewhere.
     *
     * For each .data pointer into early .text, try to DMAP-read 8 bytes
     * at that address to check for swapgs+iretq or plain iretq.
     */
    if (broad_blocked > 0 && have_text_pa) {
        send_response(sock, "\n--- Step 5b: .data Pointer Scan (XOM workaround) ---\n");
        send_response(sock, "XOM blocks %d/%d .text pages; scanning .data for early .text refs\n",
                      broad_blocked, broad_blocked + broad_readable);

        uint64_t text_va_start = (uint64_t)ktext_base;
        uint64_t text_va_early = text_va_start + 0x100000; /* first 1MB */
        uint64_t data_start = (uint64_t)KERNEL_ADDRESS_DATA_BASE;
        uint64_t data_scan_size = 0x2000000; /* 32MB */
        uint8_t dbuf[4096];

        int ptrs_found = 0;
        int ptrs_dmap_ok = 0;
        int ptrs_iretq = 0;

        #define MAX_PTR_CANDIDATES 64
        struct {
            uint64_t text_va;
            uint64_t text_pa;
            uint64_t data_addr;
            int dmap_readable;
            int is_iretq;
            int is_swapgs_iretq;
        } ptr_cands[MAX_PTR_CANDIDATES];
        int num_ptr_cands = 0;

        for (uint64_t addr = data_start;
             addr < data_start + data_scan_size;
             addr += sizeof(dbuf)) {

            int chunk_num = (int)((addr - data_start) / sizeof(dbuf));
            if (chunk_num % 2048 == 0)
                send_response(sock, "  ...%luMB\n",
                              (unsigned long)((addr - data_start) / (1024 * 1024)));

            if (kernel_copyout(addr, dbuf, sizeof(dbuf)) != 0)
                continue;

            /* Scan for 8-byte aligned pointers into early .text */
            for (int off = 0; off <= (int)sizeof(dbuf) - 8; off += 8) {
                uint64_t val;
                memcpy(&val, dbuf + off, 8);

                if (val < text_va_start || val >= text_va_early)
                    continue;
                if (val & 0x1) /* odd addresses unlikely for iretq */
                    continue;

                ptrs_found++;

                if (num_ptr_cands >= MAX_PTR_CANDIDATES)
                    continue;

                /* Translate pointer VA to PA */
                uint64_t ptr_pa = text_pa + (val - text_va_start);
                uint64_t dmap_addr = dmap_base + ptr_pa;

                int readable = 0;
                int is_iretq = 0;
                int is_swapgs_iretq = 0;

                /* Try to read 8 bytes at this .text address via DMAP */
                uint8_t code[8];
                if (kernel_copyout(dmap_addr, code, sizeof(code)) == 0) {
                    readable = 1;
                    ptrs_dmap_ok++;

                    if (code[0] == 0x48 && code[1] == 0xcf) {
                        is_iretq = 1;
                        ptrs_iretq++;
                    }
                }

                /* Also check 8 bytes before for swapgs+iretq pattern */
                if (readable && ptr_pa >= 8) {
                    uint8_t pre[8];
                    if (kernel_copyout(dmap_base + ptr_pa - 5, pre, 5) == 0) {
                        if (pre[0] == 0x0f && pre[1] == 0x01 && pre[2] == 0xf8 &&
                            pre[3] == 0x48 && pre[4] == 0xcf) {
                            is_swapgs_iretq = 1;
                        }
                    }
                }

                /* Track unique .text addresses only */
                int already = 0;
                for (int i = 0; i < num_ptr_cands; i++) {
                    if (ptr_cands[i].text_va == val) {
                        already = 1;
                        break;
                    }
                }
                if (already)
                    continue;

                ptr_cands[num_ptr_cands].text_va = val;
                ptr_cands[num_ptr_cands].text_pa = ptr_pa;
                ptr_cands[num_ptr_cands].data_addr = addr + off;
                ptr_cands[num_ptr_cands].dmap_readable = readable;
                ptr_cands[num_ptr_cands].is_iretq = is_iretq;
                ptr_cands[num_ptr_cands].is_swapgs_iretq = is_swapgs_iretq;
                num_ptr_cands++;
            }
        }

        send_response(sock, "\nPointers into early .text: %d total, %d unique\n",
                      ptrs_found, num_ptr_cands);
        send_response(sock, "DMAP readable: %d, confirmed iretq: %d\n",
                      ptrs_dmap_ok, ptrs_iretq);

        /* Report results */
        if (num_ptr_cands > 0) {
            send_response(sock, "\n%-22s %-14s %-6s %-6s %s\n",
                          "text VA", "ktext+offset", "DMAP", "iretq", "data ref");
            send_response(sock, "---------------------- -------------- ------ ------ --------\n");
        }

        for (int i = 0; i < num_ptr_cands; i++) {
            uint64_t koff = ptr_cands[i].text_va - text_va_start;
            send_response(sock, "0x%016lx   ktext+0x%-6lx %-6s %-6s kdata+0x%lx\n",
                          ptr_cands[i].text_va, koff,
                          ptr_cands[i].dmap_readable ? "YES" : "NO",
                          ptr_cands[i].is_iretq ? "YES" :
                          (ptr_cands[i].dmap_readable ? "NO" : "?"),
                          ptr_cands[i].data_addr - data_start);

            /* Promote confirmed iretq to candidate list */
            if (ptr_cands[i].is_iretq &&
                num_candidates < MAX_DORETI_CANDIDATES) {
                candidates[num_candidates].paddr = ptr_cands[i].text_pa;
                candidates[num_candidates].ktext_offset = koff;
                candidates[num_candidates].has_swapgs_before =
                    ptr_cands[i].is_swapgs_iretq;
                candidates[num_candidates].near_handler = 0;
                candidates[num_candidates].page_dist = 0x7FFFFFFF;
                num_candidates++;
            }
        }

        #undef MAX_PTR_CANDIDATES
    }

    /* ---- Step 5c: Code Reference Scan (RIP-relative to early .text) ---- */
    /*
     * When XOM blocks direct reading of early .text (where doreti_iret lives),
     * we can find it indirectly.  FreeBSD's trap() in readable .text contains:
     *
     *   if (frame->tf_rip == (long)doreti_iret)
     *       frame->tf_rip = (long)doreti_iret_fault;
     *
     * These compile to LEA reg,[rip+disp32] instructions in the readable
     * (late) portion of .text.  Since doreti_iret_fault = doreti_iret + 2
     * (sizeof iretq), finding a pair of code references whose targets are
     * exactly 2 bytes apart is a very strong signal.
     */
    if (broad_blocked > 0 && have_text_pa) {
        send_response(sock, "\n--- Step 5c: Code Reference Scan ---\n");
        send_response(sock, "Scanning readable .text for refs to early .text\n");
        send_response(sock, "  patterns: LEA [rip+disp], MOV r64 imm32 (sign-ext)\n");

        uint64_t text_va_start = (uint64_t)ktext_base;
        uint64_t text_va_early = text_va_start + 0x100000; /* first 1MB */

        #define MAX_CODE_REFS 256
        struct code_ref {
            uint64_t target_va;   /* computed target in early .text */
            uint64_t ref_va;      /* VA of referencing instruction */
        } code_refs[MAX_CODE_REFS];
        int num_code_refs = 0;
        int pages_scanned = 0;
        int lea_hits = 0, mov_hits = 0;

        for (uint64_t pa = broad_start; pa < broad_end; pa += 0x1000) {
            if (kernel_copyout(dmap_base + pa, page_buf, sizeof(page_buf)) != 0)
                continue;

            pages_scanned++;
            uint64_t page_va = text_va_start + (pa - text_pa);

            if (pages_scanned % 512 == 0)
                send_response(sock, "  ...%d pages\n", pages_scanned);

            for (size_t i = 0; i + 7 <= sizeof(page_buf); i++) {
                uint8_t b0 = page_buf[i];
                uint8_t b1 = page_buf[i + 1];
                uint8_t b2 = page_buf[i + 2];
                uint64_t target = 0;

                if ((b0 == 0x48 || b0 == 0x4c) &&
                    b1 == 0x8d && (b2 & 0xc7) == 0x05) {
                    /* LEA reg, [rip+disp32] */
                    int32_t disp;
                    memcpy(&disp, &page_buf[i + 3], 4);
                    target = (page_va + i) + 7 + (int64_t)disp;
                    if (target >= text_va_start && target < text_va_early)
                        lea_hits++;
                    else
                        target = 0;
                } else if ((b0 == 0x48 || b0 == 0x49) &&
                           b1 == 0xc7 && b2 >= 0xc0 && b2 <= 0xc7) {
                    /* MOV r64, sign_extend(imm32) */
                    int32_t imm32;
                    memcpy(&imm32, &page_buf[i + 3], 4);
                    target = (uint64_t)(int64_t)imm32;
                    if (target >= text_va_start && target < text_va_early)
                        mov_hits++;
                    else
                        target = 0;
                }

                if (target == 0)
                    continue;

                if (num_code_refs < MAX_CODE_REFS) {
                    code_refs[num_code_refs].target_va = target;
                    code_refs[num_code_refs].ref_va = page_va + i;
                    num_code_refs++;
                }
            }
        }

        send_response(sock, "Scanned %d readable pages, found %d refs "
                      "(LEA: %d, MOV: %d)\n",
                      pages_scanned, num_code_refs, lea_hits, mov_hits);

        if (num_code_refs >= MAX_CODE_REFS)
            send_response(sock, "  (hit limit of %d, some refs may be missing)\n",
                          MAX_CODE_REFS);

        /* Collect unique target addresses with reference counts */
        #define MAX_UNIQ_TARGETS 128
        struct {
            uint64_t va;
            int      ref_count;
        } uniq[MAX_UNIQ_TARGETS];
        int num_uniq = 0;

        for (int i = 0; i < num_code_refs; i++) {
            int found = 0;
            for (int j = 0; j < num_uniq; j++) {
                if (uniq[j].va == code_refs[i].target_va) {
                    uniq[j].ref_count++;
                    found = 1;
                    break;
                }
            }
            if (!found && num_uniq < MAX_UNIQ_TARGETS) {
                uniq[num_uniq].va = code_refs[i].target_va;
                uniq[num_uniq].ref_count = 1;
                num_uniq++;
            }
        }

        send_response(sock, "Unique target addresses: %d\n", num_uniq);

        /* Detect pairs: target_B = target_A + 2 (doreti_iret / doreti_iret_fault) */
        uint64_t best_doreti = 0;
        int best_pair_refs = 0;
        int pair_count = 0;

        for (int a = 0; a < num_uniq; a++) {
            for (int b = 0; b < num_uniq; b++) {
                if (a == b)
                    continue;
                if (uniq[b].va != uniq[a].va + 2)
                    continue;

                pair_count++;
                int total_refs = uniq[a].ref_count + uniq[b].ref_count;

                send_response(sock,
                    "\n  PAIR #%d (refs: %d+%d):\n"
                    "    doreti_iret       = 0x%lx (ktext+0x%lx)\n"
                    "    doreti_iret_fault = 0x%lx (ktext+0x%lx)\n",
                    pair_count, uniq[a].ref_count, uniq[b].ref_count,
                    uniq[a].va, uniq[a].va - text_va_start,
                    uniq[b].va, uniq[b].va - text_va_start);

                /* Show where the references come from */
                for (int r = 0; r < num_code_refs; r++) {
                    if (code_refs[r].target_va == uniq[a].va ||
                        code_refs[r].target_va == uniq[b].va) {
                        const char *which = (code_refs[r].target_va == uniq[a].va)
                                            ? "iret" : "fault";
                        send_response(sock, "      ref %s @ ktext+0x%lx\n",
                                      which,
                                      code_refs[r].ref_va - text_va_start);
                    }
                }

                if (total_refs > best_pair_refs) {
                    best_pair_refs = total_refs;
                    best_doreti = uniq[a].va;
                }
            }
        }

        if (best_doreti) {
            uint64_t koff = best_doreti - text_va_start;

            send_response(sock,
                "\n*** doreti_iret = 0x%lx (ktext+0x%lx) ***\n",
                best_doreti, koff);
            send_response(sock,
                "*** doreti_iret_fault = 0x%lx (ktext+0x%lx) ***\n",
                best_doreti + 2, koff + 2);
            send_response(sock, "Confidence: HIGH (RIP-relative pair, 2 bytes apart)\n");
            send_response(sock, "\nNotes:\n");
            send_response(sock, "  Found via LEA [rip+disp] in trap() or trap_fatal()\n");
            send_response(sock, "  doreti_iret_fault = doreti_iret + 2 (sizeof iretq)\n");
            send_response(sock, "  Phase 7c will redirect #DB to singlestep "
                          "through this instruction\n");
            send_response(sock, "OK\n");
            return;
        }

        /* No pairs - show top referenced targets as fallback */
        if (num_uniq > 0) {
            send_response(sock, "\nNo 2-byte pairs found. "
                          "Top referenced early .text addresses:\n");
            send_response(sock, "%-22s %-14s %s\n",
                          "target VA", "ktext+offset", "refs");
            /* Simple selection sort for top 15 */
            for (int shown = 0; shown < 15 && shown < num_uniq; shown++) {
                int best = -1, best_rc = 0;
                for (int j = 0; j < num_uniq; j++) {
                    if (uniq[j].ref_count > best_rc) {
                        best_rc = uniq[j].ref_count;
                        best = j;
                    }
                }
                if (best < 0)
                    break;
                send_response(sock, "0x%016lx   ktext+0x%-6lx %d\n",
                              uniq[best].va,
                              uniq[best].va - text_va_start,
                              uniq[best].ref_count);
                uniq[best].ref_count = -1;
            }
        }

        #undef MAX_CODE_REFS
        #undef MAX_UNIQ_TARGETS
    }

    /* ---- Step 7: #GP Trap Frame Method (sleirsgoevy's technique) ---- */
    /*
     * When all previous steps fail (full XOM), use a race-condition technique:
     *   1. Find the TSS in kernel .data, read IST entries
     *   2. Allocate a user page and find its PA via process CR3
     *   3. Redirect the TSS IST entry to our DMAP-backed page
     *   4. Trigger iretq with non-canonical RIP -> #GP
     *   5. Writer thread overwrites CS on our IST page -> SIGBUS to userspace
     *   6. Signal handler reads doreti_iret from mc_rip
     *
     * Trigger when: no candidates at all, OR all candidates are low-confidence
     * (no swapgs, no handler proximity => none would classify as LIKELY/POSSIBLE).
     */
    {
        int have_strong_candidate = 0;
        for (int c = 0; c < num_candidates; c++) {
            int near_gp = (candidates[c].near_handler == 13 &&
                           candidates[c].page_dist <= 16);
            if (candidates[c].has_swapgs_before || near_gp) {
                have_strong_candidate = 1;
                break;
            }
        }

    if (!have_strong_candidate && have_text_pa) {
        send_response(sock, "\n--- Step 7: #GP Trap Frame Method ---\n");
        if (num_candidates == 0)
            send_response(sock, "No candidates from previous steps; trying IST race.\n\n");
        else
            send_response(sock, "All %d candidates are low-confidence (no swapgs, no handler "
                          "proximity); trying IST race.\n\n", num_candidates);

        /* State for cleanup */
        void *ist_page = NULL;
        void *sigalt_stack = NULL;
        uint64_t tss_va = 0;
        int tss_stride = 0;
        #define GP_TRAP_MAX_CPUS 8
        int ist_modified_percpu[GP_TRAP_MAX_CPUS][7];
        uint64_t ist_saved_percpu[GP_TRAP_MAX_CPUS][7];
        memset(ist_modified_percpu, 0, sizeof(ist_modified_percpu));
        memset(ist_saved_percpu, 0, sizeof(ist_saved_percpu));
        int idt_gate_modified = 0;
        uint8_t idt_gate_saved[16];
        int ss_gate_modified = 0;
        uint8_t ss_gate_saved[16];
        int gp_ist_index = 0; /* which IST the #GP gate uses (0 = none) */
        int cpu_pinned = 0;
        int sigbus_installed = 0;
        struct sigaction old_sigbus_act;
        int sigsegv_installed = 0;
        struct sigaction old_sigsegv_act;
        int writer_started = 0;
        thrd_t writer_thread;
        stack_t old_sigalt;
        int had_old_sigalt = 0;

        /* 7a. Find TSS */
        send_response(sock, "7a. Finding TSS in kernel .data...\n");
        tss_va = find_tss_in_kdata(sock, &tss_stride);
        if (tss_va == 0) {
            send_response(sock, "TSS not found, cannot proceed with Step 7\n");
            goto step7_cleanup;
        }
        send_response(sock, "  TSS stride: %d bytes\n", tss_stride);

        /* Read all IST entries from TSS */
        uint64_t ist_entries[7];
        for (int i = 0; i < 7; i++) {
            ist_entries[i] = kernel_getlong(tss_va + 0x24 + i * 8);
            send_response(sock, "  TSS IST%d: 0x%lx\n", i + 1, ist_entries[i]);
        }

        /* 7b. Find IDT by scanning kernel .data for the r_idt descriptor.
         *
         * FreeBSD stores the IDTR in a global `struct region_descriptor r_idt`
         * (10 bytes packed: uint16_t limit + uint64_t base). For a standard
         * 256-entry IDT: limit = 0x0FFF, base = kernel VA of the IDT table.
         * We scan .data for this pattern, then validate by reading a few
         * gate entries from the candidate base.
         *
         * Note: SIDT is trapped by the PS5 hypervisor, so we cannot use it.
         */
        send_response(sock, "\n7b. Finding IDT...\n");
        if (idt_base != 0) {
            send_response(sock, "  Using IDT from Step 1: 0x%lx\n", idt_base);
        } else {
            uint64_t kdata = (uint64_t)KERNEL_ADDRESS_DATA_BASE;
            uint64_t ktext = (uint64_t)KERNEL_ADDRESS_TEXT_BASE;
            uint64_t scan_size = 0x4000000; /* 64MB: matches TSS scan range */
            uint64_t dmap_base = get_dmap_base();
            uint64_t pm_cr3 = get_kernel_cr3();
            uint8_t page[4096];
            int idt_found = 0;
            int ridt_candidates_total = 0;
            int ridt_candidates_rejected = 0;
            int ridt_probed = 0;

            for (uint64_t addr = kdata;
                 addr < kdata + scan_size && !idt_found;
                 addr += 4096) {
                if (((addr - kdata) & 0x7FFFFF) == 0 && addr != kdata)
                    send_response(sock, "  ...%luMB\n",
                                  (unsigned long)((addr - kdata) >> 20));
                if (kernel_copyout(addr, page, 4096) != 0)
                    continue;

                /* Scan for limit=0x0FFF followed by kernel address */
                for (int off = 0; off + 10 <= 4096 && !idt_found; off += 2) {
                    uint16_t limit;
                    uint64_t base;
                    memcpy(&limit, page + off, 2);
                    if (limit != 0x0FFF)
                        continue;
                    memcpy(&base, page + off + 2, 8);
                    if (base < 0xFFFF800000000000ULL)
                        continue;

                    ridt_candidates_total++;
                    /* IDT entries are 16 bytes; base must be aligned. */
                    if (base & 0xF)
                        continue;

                    /* Read IDT gates from candidate base.
                     * For addresses in the ktext..kdata range (may be
                     * XOM), translate to physical and read via DMAP to
                     * avoid hypervisor trap on direct read. */
                    uint8_t gates[64]; /* first 4 entries */
                    int read_ok = 0;
                    int in_text_range = (base >= ktext && base < kdata);
                    if (in_text_range) {
                        uint64_t paddr = 0;
                        int xlat = vaddr_to_paddr_quiet(dmap_base,
                            pm_cr3, base, &paddr, NULL);
                        if (xlat == 0) {
                            int rc = kernel_copyout(
                                dmap_base + paddr, gates, 64);
                            read_ok = (rc == 0);
                            if (ridt_candidates_rejected < 3)
                                send_response(sock,
                                    "  DMAP probe: base=0x%lx "
                                    "pa=0x%lx rc=%d\n",
                                    base, paddr, rc);
                        } else if (ridt_candidates_rejected < 3) {
                            send_response(sock,
                                "  xlat fail: base=0x%lx\n", base);
                        }
                    } else {
                        read_ok = (kernel_copyout(base, gates, 64) == 0);
                        if (!read_ok && ridt_candidates_rejected < 3)
                            send_response(sock,
                                "  direct fail: base=0x%lx\n", base);
                    }
                    if (!read_ok) {
                        ridt_candidates_rejected++;
                        continue;
                    }
                    ridt_probed++;
                    int valid = 0;
                    for (int v = 0; v < 4; v++) {
                        uint8_t *g = gates + v * 16;
                        /* Check present bit + gate type */
                        if (!(g[5] & 0x80))
                            continue;
                        uint8_t type = g[5] & 0x0F;
                        if (type != 14 && type != 15)
                            continue;
                        /* Check reserved bytes 12-15 are zero */
                        uint32_t rsvd;
                        memcpy(&rsvd, g + 12, 4);
                        if (rsvd != 0)
                            continue;
                        /* Check handler is kernel address */
                        uint64_t h = (uint64_t)g[0] |
                                     ((uint64_t)g[1] << 8) |
                                     ((uint64_t)g[6] << 16) |
                                     ((uint64_t)g[7] << 24) |
                                     ((uint64_t)g[8] << 32) |
                                     ((uint64_t)g[9] << 40) |
                                     ((uint64_t)g[10] << 48) |
                                     ((uint64_t)g[11] << 56);
                        if (h >= 0xFFFF800000000000ULL)
                            valid++;
                    }

                    if (valid >= 3) {
                        idt_base = base;
                        idt_found = 1;
                        /* Set access address: use DMAP for XOM range */
                        if (base >= ktext && base < kdata) {
                            uint64_t pa;
                            if (vaddr_to_paddr_quiet(dmap_base, pm_cr3,
                                                     base, &pa,
                                                     NULL) == 0)
                                idt_access = dmap_base + pa;
                            else
                                idt_access = base; /* shouldn't happen */
                        } else {
                            idt_access = base;
                        }
                        uint16_t sel;
                        memcpy(&sel, gates + 2, 2);
                        send_response(sock,
                            "  r_idt at kdata+0x%lx: limit=0x%x "
                            "base=0x%lx access=0x%lx (CS=0x%04x)\n",
                            (unsigned long)(addr + off - kdata),
                            limit, base, idt_access, sel);
                    } else if (ridt_probed <= 10) {
                        send_response(sock,
                            "  r_idt probe: base=0x%lx "
                            "valid=%d/4 g[5]=%02x%02x%02x%02x\n",
                            base, valid,
                            gates[5], gates[21], gates[37], gates[53]);
                    }
                }
            }

            /* Fallback: direct IDT gate pattern scan.
             * Checks every 16-byte-aligned offset in each page,
             * not just offset 0 — IDT may not be page-aligned. */
            if (!idt_found) {
                send_response(sock, "  r_idt not found; scanning for "
                              "IDT gate patterns...\n");
                for (uint64_t addr = kdata;
                     addr < kdata + scan_size && !idt_found;
                     addr += 4096) {
                    if (((addr - kdata) & 0x7FFFFF) == 0 && addr != kdata)
                        send_response(sock, "  ...%luMB\n",
                                      (unsigned long)((addr - kdata) >> 20));
                    if (kernel_copyout(addr, page, 4096) != 0)
                        continue;

                    /* Check every 16-byte-aligned offset (need 64B) */
                    for (int poff = 0;
                         poff + 64 <= 4096 && !idt_found;
                         poff += 16) {
                        int valid = 0;
                        for (int v = 0; v < 4; v++) {
                            uint8_t *g = page + poff + v * 16;
                            if (!(g[5] & 0x80))
                                continue;
                            uint8_t type = g[5] & 0x0F;
                            if (type != 14 && type != 15)
                                continue;
                            uint32_t rsvd;
                            memcpy(&rsvd, g + 12, 4);
                            if (rsvd != 0)
                                continue;
                            uint64_t h = (uint64_t)g[0] |
                                         ((uint64_t)g[1] << 8) |
                                         ((uint64_t)g[6] << 16) |
                                         ((uint64_t)g[7] << 24) |
                                         ((uint64_t)g[8] << 32) |
                                         ((uint64_t)g[9] << 40) |
                                         ((uint64_t)g[10] << 48) |
                                         ((uint64_t)g[11] << 56);
                            if (h >= 0xFFFF800000000000ULL)
                                valid++;
                        }
                        if (valid >= 3) {
                            idt_base = addr + poff;
                            idt_access = idt_base; /* in .data — direct */
                            idt_found = 1;
                            uint16_t sel;
                            memcpy(&sel, page + poff + 2, 2);
                            send_response(sock,
                                "  IDT gates at kdata+0x%lx (%d/4 "
                                "valid, CS=0x%04x)\n",
                                (unsigned long)(addr + poff - kdata),
                                valid, sel);
                        }
                    }
                }
            }

            if (!idt_found) {
                send_response(sock, "  IDT not in kernel .data; "
                              "brute-force scanning physical memory "
                              "via DMAP...\n");
                send_response(sock, "  Diag: kdata=0x%lx ktext=0x%lx "
                              "dmap=0x%lx\n", kdata, ktext, dmap_base);
                send_response(sock, "  Diag: r_idt candidates=%d "
                              "rejected=%d probed=%d\n",
                              ridt_candidates_total,
                              ridt_candidates_rejected,
                              ridt_probed);

                /* Brute-force: scan physical memory 0..4GB via DMAP
                 * looking for IDT gate patterns at any 16-byte offset.
                 * The IDT must exist in physical RAM; even if the HV
                 * hides it from the kernel's VA space, DMAP may still
                 * map those physical pages.  The IDT PA varies per boot
                 * due to KASLR (observed at ~448MB on one run). */
                uint64_t phys_scan_end = 0x100000000ULL; /* 4GB */
                int phys_pages_read = 0;
                int phys_pages_fail = 0;
                for (uint64_t pa = 0;
                     pa < phys_scan_end && !idt_found;
                     pa += 4096) {
                    if ((pa & 0x3FFFFFF) == 0)
                        send_response(sock, "  ...PA %luMB/%luMB\n",
                            (unsigned long)(pa >> 20),
                            (unsigned long)(phys_scan_end >> 20));
                    if (kernel_copyout(dmap_base + pa,
                                       page, 4096) != 0) {
                        phys_pages_fail++;
                        continue;
                    }
                    phys_pages_read++;

                    for (int poff = 0;
                         poff + 64 <= 4096 && !idt_found;
                         poff += 16) {
                        int valid = 0;
                        for (int v = 0; v < 4; v++) {
                            uint8_t *g = page + poff + v * 16;
                            if (!(g[5] & 0x80))
                                continue;
                            uint8_t type = g[5] & 0x0F;
                            if (type != 14 && type != 15)
                                continue;
                            uint32_t rsvd;
                            memcpy(&rsvd, g + 12, 4);
                            if (rsvd != 0)
                                continue;
                            uint64_t h = (uint64_t)g[0] |
                                ((uint64_t)g[1] << 8) |
                                ((uint64_t)g[6] << 16) |
                                ((uint64_t)g[7] << 24) |
                                ((uint64_t)g[8] << 32) |
                                ((uint64_t)g[9] << 40) |
                                ((uint64_t)g[10] << 48) |
                                ((uint64_t)g[11] << 56);
                            if (h >= 0xFFFF800000000000ULL)
                                valid++;
                        }
                        if (valid >= 3) {
                            idt_found = 1;
                            idt_base = dmap_base + pa + poff;
                            idt_access = idt_base; /* via DMAP */
                            uint16_t sel;
                            memcpy(&sel, page + poff + 2, 2);
                            send_response(sock,
                                "  IDT found at PA 0x%lx+0x%x "
                                "(%d/4 valid, CS=0x%04x) "
                                "[%d pages read, %d failed]\n",
                                pa, poff, valid, sel,
                                phys_pages_read,
                                phys_pages_fail);
                        }
                    }
                }

                if (!idt_found) {
                    send_response(sock,
                        "  DMAP brute-force: no IDT in %luMB "
                        "(%d read, %d failed)\n",
                        (unsigned long)(phys_scan_end >> 20),
                        phys_pages_read, phys_pages_fail);
                    goto step7_cleanup;
                }
            }
        }

        /* Read #GP gate (vector 13) */
        {
            uint8_t gp_gate[16];
            if (kernel_copyout(idt_access + 13 * 16, gp_gate, 16) != 0) {
                send_response(sock, "  Cannot read #GP gate\n");
                goto step7_cleanup;
            }

            gp_ist_index = gp_gate[4] & 0x07;
            uint64_t gp_handler =
                (uint64_t)gp_gate[0] |
                ((uint64_t)gp_gate[1] << 8) |
                ((uint64_t)gp_gate[6] << 16) |
                ((uint64_t)gp_gate[7] << 24) |
                ((uint64_t)gp_gate[8] << 32) |
                ((uint64_t)gp_gate[9] << 40) |
                ((uint64_t)gp_gate[10] << 48) |
                ((uint64_t)gp_gate[11] << 56);

            send_response(sock, "  #GP gate: handler=0x%lx IST=%d "
                          "type=0x%02x\n",
                          gp_handler, gp_ist_index, gp_gate[5]);
        }

        /* 7c. Allocate IST page */
        send_response(sock, "\n7c. Allocating IST page...\n");
        ist_page = mmap(NULL, 4096, PROT_READ | PROT_WRITE,
                        MAP_PRIVATE | MAP_ANON, -1, 0);
        if (ist_page == MAP_FAILED) {
            ist_page = NULL;
            send_response(sock, "  mmap failed\n");
            goto step7_cleanup;
        }
        memset(ist_page, 0, 4096);
        send_response(sock, "  IST page at user VA %p\n", ist_page);

        /* 7d. Find physical address of IST page */
        send_response(sock, "\n7d. Finding IST page physical address...\n");
        uint64_t ist_page_pa = find_user_page_pa(sock, dmap_base, ist_page);
        if (ist_page_pa == 0) {
            send_response(sock, "  Cannot find IST page PA\n");
            goto step7_cleanup;
        }
        uint64_t ist_dmap_va = dmap_base + ist_page_pa;
        uint64_t ist_stack_top = ist_dmap_va + 0x1000;
        send_response(sock, "  IST page PA=0x%lx, DMAP VA=0x%lx, stack top=0x%lx\n",
                      ist_page_pa, ist_dmap_va, ist_stack_top);

        /* 7e. Patch #GP (vec 13) and #SS (vec 12) gates to use IST7.
         *
         * Non-canonical RIP during iretq → #GP(0).
         * Non-canonical RSP during iretq → #SS(0) on AMD, #GP(0) on some.
         * We patch BOTH gates so either fault vector uses our IST page.
         */
        send_response(sock, "\n7e. Configuring IST for #GP and #SS...\n");
        if (gp_ist_index == 0) {
            /* #GP gate has no IST — patch it to use IST7 */
            send_response(sock, "  #GP gate IST=0; patching to IST7\n");
            if (kernel_copyout(idt_access + 13 * 16, idt_gate_saved, 16) == 0) {
                uint8_t new_ist_byte = (idt_gate_saved[4] & 0xF8) | 7;
                kernel_setchar(idt_access + 13 * 16 + 4, new_ist_byte);
                idt_gate_modified = 1;
                gp_ist_index = 7;
                send_response(sock, "  Patched #GP gate IST: 0 -> 7\n");
            } else {
                send_response(sock, "  Cannot read #GP gate for patching\n");
                goto step7_cleanup;
            }
        } else {
            send_response(sock, "  #GP gate already uses IST%d\n", gp_ist_index);
        }
        /* Also patch #SS gate (vector 12) to use IST7 */
        {
            uint8_t ss_gate[16];
            if (kernel_copyout(idt_access + 12 * 16, ss_gate, 16) == 0) {
                int ss_ist = ss_gate[4] & 0x07;
                uint64_t ss_handler =
                    (uint64_t)ss_gate[0] |
                    ((uint64_t)ss_gate[1] << 8) |
                    ((uint64_t)ss_gate[6] << 16) |
                    ((uint64_t)ss_gate[7] << 24) |
                    ((uint64_t)ss_gate[8] << 32) |
                    ((uint64_t)ss_gate[9] << 40) |
                    ((uint64_t)ss_gate[10] << 48) |
                    ((uint64_t)ss_gate[11] << 56);
                send_response(sock, "  #SS gate: handler=0x%lx IST=%d type=0x%02x\n",
                              ss_handler, ss_ist, ss_gate[5]);
                if (ss_ist == 0) {
                    memcpy(ss_gate_saved, ss_gate, 16);
                    uint8_t new_ss_byte = (ss_gate[4] & 0xF8) | 7;
                    kernel_setchar(idt_access + 12 * 16 + 4, new_ss_byte);
                    ss_gate_modified = 1;
                    send_response(sock, "  Patched #SS gate IST: 0 -> 7\n");
                } else {
                    send_response(sock, "  #SS gate already uses IST%d\n", ss_ist);
                }
            } else {
                send_response(sock, "  WARNING: cannot read #SS gate\n");
            }
        }

        /* Set the target IST entry on all per-CPU TSSes */
        {
            int idx = gp_ist_index - 1;
            send_response(sock, "  Setting IST%d on all CPUs to 0x%lx\n",
                          gp_ist_index, ist_stack_top);
            for (int cpu = 0; cpu < GP_TRAP_MAX_CPUS && tss_stride > 0; cpu++) {
                uint64_t cpu_tss = tss_va + (uint64_t)cpu * tss_stride;
                uint32_t rsvd0;
                uint64_t rsp0;
                if (kernel_copyout(cpu_tss, &rsvd0, 4) != 0 || rsvd0 != 0)
                    break;
                if (kernel_copyout(cpu_tss + 4, &rsp0, 8) != 0 || rsp0 == 0)
                    break;
                ist_saved_percpu[cpu][idx] = kernel_getlong(cpu_tss + 0x24 + idx * 8);
                kernel_setlong(cpu_tss + 0x24 + idx * 8, ist_stack_top);
                ist_modified_percpu[cpu][idx] = 1;
                send_response(sock, "  CPU%d TSS 0x%lx: IST%d -> 0x%lx (was 0x%lx)\n",
                              cpu, cpu_tss, gp_ist_index, ist_stack_top,
                              ist_saved_percpu[cpu][idx]);
            }
        }

        /* 7f. Pin to CPU 0 (cascading fallback) */
        send_response(sock, "\n7f. Pinning to CPU 0...\n");
        {
            cpuset_t cpuset;
            CPU_ZERO(&cpuset);
            CPU_SET(0, &cpuset);

            /* Strategy 1: CPU_WHICH_PID with full cpuset_t */
            if (cpuset_setaffinity(CPU_LEVEL_WHICH, CPU_WHICH_PID, getpid(),
                                   sizeof(cpuset), &cpuset) == 0) {
                cpu_pinned = 1;
                send_response(sock, "  Pinned via CPU_WHICH_PID (size=%zu)\n",
                              sizeof(cpuset));
            }

            /* Strategy 2: CPU_WHICH_PID with 8-byte mask */
            if (!cpu_pinned) {
                unsigned long small_mask = 1; /* bit 0 = CPU 0 */
                if (cpuset_setaffinity(CPU_LEVEL_WHICH, CPU_WHICH_PID, getpid(),
                                       sizeof(small_mask),
                                       (const cpuset_t *)&small_mask) == 0) {
                    cpu_pinned = 1;
                    send_response(sock, "  Pinned via small cpuset (8 bytes)\n");
                } else {
                    send_response(sock, "  small cpuset failed (errno=%d)\n", errno);
                }
            }

            /* Strategy 3: pthread_setaffinity_np */
            if (!cpu_pinned) {
                pthread_t self = pthread_self();
                if (pthread_setaffinity_np(self, sizeof(cpuset), &cpuset) == 0) {
                    cpu_pinned = 1;
                    send_response(sock, "  Pinned via pthread_setaffinity_np\n");
                } else {
                    send_response(sock, "  pthread_setaffinity_np failed (errno=%d)\n",
                                  errno);
                }
            }

            /* Strategy 4: CPU_WHICH_TID (original) */
            if (!cpu_pinned) {
                if (cpuset_setaffinity(CPU_LEVEL_WHICH, CPU_WHICH_TID, -1,
                                       sizeof(cpuset), &cpuset) == 0) {
                    cpu_pinned = 1;
                    send_response(sock, "  Pinned via CPU_WHICH_TID\n");
                } else {
                    send_response(sock, "  CPU_WHICH_TID failed (errno=%d)\n", errno);
                }
            }

            if (!cpu_pinned) {
                send_response(sock, "  WARNING: all pinning strategies failed\n");
                send_response(sock, "  Continuing - all per-CPU TSSes were modified\n");
            }
        }

        /* 7g. Setup signal handling */
        send_response(sock, "\n7g. Setting up signal handling...\n");
        {
            /* Allocate signal alternate stack (64KB) */
            size_t sigstack_size = 64 * 1024;
            sigalt_stack = mmap(NULL, sigstack_size, PROT_READ | PROT_WRITE,
                                MAP_PRIVATE | MAP_ANON, -1, 0);
            if (sigalt_stack == MAP_FAILED) {
                sigalt_stack = NULL;
                send_response(sock, "  sigaltstack mmap failed\n");
                goto step7_cleanup;
            }

            stack_t ss;
            ss.ss_sp = sigalt_stack;
            ss.ss_size = sigstack_size;
            ss.ss_flags = 0;
            if (sigaltstack(&ss, &old_sigalt) == 0) {
                had_old_sigalt = 1;
            } else {
                send_response(sock, "  WARNING: sigaltstack failed\n");
            }

            struct sigaction sa;
            memset(&sa, 0, sizeof(sa));
            sa.sa_sigaction = gp_trap_fault_handler;
            sigemptyset(&sa.sa_mask);
            sa.sa_flags = SA_SIGINFO | SA_ONSTACK;
            if (sigaction(SIGBUS, &sa, &old_sigbus_act) == 0) {
                sigbus_installed = 1;
                send_response(sock, "  SIGBUS handler installed (SA_ONSTACK)\n");
            } else {
                send_response(sock, "  SIGBUS sigaction failed\n");
                goto step7_cleanup;
            }
            if (sigaction(SIGSEGV, &sa, &old_sigsegv_act) == 0) {
                sigsegv_installed = 1;
                send_response(sock, "  SIGSEGV handler installed (SA_ONSTACK)\n");
            } else {
                send_response(sock, "  WARNING: SIGSEGV sigaction failed\n");
            }
        }

        /* 7h. Start writer thread */
        send_response(sock, "\n7h. Starting writer thread...\n");
        gp_trap_stop_writer = 0;
        gp_trap_got_result = 0;
        gp_trap_doreti_addr = 0;

        if (thrd_create(&writer_thread, gp_trap_writer_fn, ist_page) == thrd_success) {
            writer_started = 1;
            send_response(sock, "  Writer thread started (target: ist_page+0xFE0)\n");
        } else {
            send_response(sock, "  thrd_create failed\n");
            goto step7_cleanup;
        }

        /* 7i. Trigger loop
         *
         * Two strategies to fault at doreti_iret:
         * A) Non-canonical RSP → #SS(0) on AMD, #GP(0) on some CPUs
         * B) Non-canonical RIP → #GP(0)
         *
         * Both cause a fault AT the iretq instruction (doreti_iret).
         * The CPU pushes a trap frame onto our IST page via DMAP.
         * The RIP field (page+0xFD8) = doreti_iret.
         *
         * Primary path: read doreti_iret directly from IST page after
         * the fault returns to us (the kernel handles the fault at
         * doreti_iret silently and resumes userspace at getcontext's
         * save point).
         *
         * Secondary path: if the writer thread wins the CS race, the
         * kernel delivers a signal and our handler captures mc_rip.
         *
         * Note: setcontext success jumps to getcontext's return point,
         * bypassing the while-condition.  We enforce the limit with an
         * explicit check after the counter increment.
         */
        send_response(sock, "\n7i. Triggering iretq fault (up to 50 attempts)...\n");
        {
            int max_attempts = 50;
            gp_trap_attempt_count = 0;
            gp_trap_sig_received = 0;
            volatile uint8_t *istp = (volatile uint8_t *)ist_page;

            /* Clear IST trap frame area (0xFD0..0xFFF) */
            for (int i = 0xFD0; i < 0x1000; i++)
                istp[i] = 0;

            if (sigsetjmp(gp_trap_jmp_env, 1) != 0) {
                /* Returned from signal handler via siglongjmp
                 * (writer thread won the CS race) */
                send_response(sock, "  attempt %d: signal %d (%s) caught! "
                              "mc_rip=0x%lx mc_cs=0x%lx mc_err=0x%lx\n",
                              (int)gp_trap_attempt_count,
                              (int)gp_trap_sig_received,
                              gp_trap_sig_received == SIGBUS ? "SIGBUS" :
                              gp_trap_sig_received == SIGSEGV ? "SIGSEGV" : "?",
                              (uint64_t)gp_trap_doreti_addr,
                              (uint64_t)gp_trap_mc_cs,
                              (uint64_t)gp_trap_mc_err);
            } else {
                while (!gp_trap_got_result &&
                       gp_trap_attempt_count < max_attempts) {
                    ucontext_t uc;
                    getcontext(&uc);
                    gp_trap_attempt_count++;

                    if (gp_trap_got_result)
                        break;

                    /* Enforce limit — setcontext bypasses while-cond */
                    if (gp_trap_attempt_count > max_attempts)
                        break;

                    /* Check IST page for doreti_iret from a fault.
                     * CPU pushes RIP at IST_top - 0x28 = page+0xFD8.
                     * The value persists after the kernel handles the
                     * fault and returns to us. */
                    {
                        uint64_t rip_val = *(volatile uint64_t *)(istp + 0xFD8);
                        uint64_t cs_val  = *(volatile uint64_t *)(istp + 0xFE0);
                        uint64_t err_val = *(volatile uint64_t *)(istp + 0xFD0);
                        uint64_t fl_val  = *(volatile uint64_t *)(istp + 0xFE8);
                        uint64_t rsp_val = *(volatile uint64_t *)(istp + 0xFF0);
                        uint64_t ss_val  = *(volatile uint64_t *)(istp + 0xFF8);

                        /* Dump IST frame for first 3 attempts */
                        if (gp_trap_attempt_count <= 3) {
                            send_response(sock,
                                "  IST@%d: err=%lx RIP=%lx CS=%lx "
                                "FL=%lx RSP=%lx SS=%lx\n",
                                (int)gp_trap_attempt_count,
                                err_val, rip_val, cs_val,
                                fl_val, rsp_val, ss_val);
                        }

                        if (rip_val >= 0xFFFF800000000000ULL &&
                            rip_val != 0xFFFFFFFFFFFFFFFFULL) {
                            /* Found kernel address — this is doreti_iret */
                            gp_trap_doreti_addr = rip_val;
                            gp_trap_mc_cs  = cs_val;
                            gp_trap_mc_err = err_val;
                            gp_trap_got_result = 1;
                            gp_trap_sig_received = -1; /* IST read */
                            send_response(sock,
                                "  attempt %d: IST page read: "
                                "RIP=0x%lx CS=0x%lx err=0x%lx\n",
                                (int)gp_trap_attempt_count,
                                rip_val, cs_val, err_val);
                            break;
                        }
                    }

                    const char *strategy;
                    if (gp_trap_attempt_count <= 25) {
                        /* Strategy A: non-canonical RSP.
                         * Keep RIP valid; iretq faults loading RSP.
                         * AMD: #SS(0), some CPUs: #GP(0). */
                        uc.uc_mcontext.mc_rsp = 0x8000000000000000ULL;
                        strategy = "non-canonical RSP";
                    } else {
                        /* Strategy B: non-canonical RIP.
                         * iretq faults loading RIP → #GP(0). */
                        uc.uc_mcontext.mc_rip = 0x8000000000000000ULL;
                        strategy = "non-canonical RIP";
                    }

                    if (gp_trap_attempt_count == 1 ||
                        gp_trap_attempt_count == 26 ||
                        (gp_trap_attempt_count % 10) == 0) {
                        send_response(sock, "  attempt %d (%s)...\n",
                                      (int)gp_trap_attempt_count, strategy);
                    }

                    setcontext(&uc);

                    /* setcontext returned — kernel rejected the context.
                     * Log first few failures per strategy. */
                    if (gp_trap_attempt_count <= 2 ||
                        gp_trap_attempt_count == 26 ||
                        (gp_trap_attempt_count % 10) == 0) {
                        send_response(sock, "  setcontext returned at "
                                      "attempt %d (%s, errno=%d)\n",
                                      (int)gp_trap_attempt_count,
                                      strategy, errno);
                    }
                    usleep(100); /* yield briefly between retries */
                }
            }
        }

        /* 7j. Report result */
        send_response(sock, "\n7j. Result:\n");
        if (gp_trap_got_result && gp_trap_doreti_addr != 0) {
            uint64_t addr = gp_trap_doreti_addr;
            uint64_t koff = addr - (uint64_t)ktext_base;

            /* Validate: should be in kernel .text range */
            if (addr >= (uint64_t)ktext_base &&
                addr < (uint64_t)ktext_base + 0x2000000) {
                send_response(sock,
                    "\n*** doreti_iret = 0x%lx (ktext+0x%lx) ***\n",
                    addr, koff);
                send_response(sock,
                    "Confidence: HIGH (direct trap frame intercept)\n");
                send_response(sock, "\nNotes:\n");
                if (gp_trap_sig_received == -1) {
                    send_response(sock,
                        "  Method: direct IST page read (no signal needed)\n"
                        "  mc_cs=0x%lx mc_err=0x%lx\n",
                        (uint64_t)gp_trap_mc_cs, (uint64_t)gp_trap_mc_err);
                } else {
                    send_response(sock,
                        "  Signal: %d (%s)  mc_cs=0x%lx mc_err=0x%lx\n",
                        (int)gp_trap_sig_received,
                        gp_trap_sig_received == SIGBUS ? "SIGBUS" :
                        gp_trap_sig_received == SIGSEGV ? "SIGSEGV" : "?",
                        (uint64_t)gp_trap_mc_cs, (uint64_t)gp_trap_mc_err);
                }
                send_response(sock,
                    "  Found via sleirsgoevy's IST technique\n");
                send_response(sock,
                    "  Phase 7c will redirect #DB to singlestep "
                    "through this instruction\n");

                /* Stop writer before cleanup */
                gp_trap_stop_writer = 1;
                if (writer_started) {
                    thrd_join(writer_thread, NULL);
                    writer_started = 0;
                }

                /* Cleanup per-CPU TSS IST entries */
                for (int cpu = 0; cpu < GP_TRAP_MAX_CPUS; cpu++) {
                    for (int i = 0; i < 7; i++) {
                        if (ist_modified_percpu[cpu][i]) {
                            uint64_t cpu_tss = tss_va + (uint64_t)cpu * tss_stride;
                            kernel_setlong(cpu_tss + 0x24 + i * 8,
                                           ist_saved_percpu[cpu][i]);
                            ist_modified_percpu[cpu][i] = 0;
                        }
                    }
                }
                /* Cleanup IDT gates */
                if (idt_gate_modified) {
                    kernel_setchar(idt_access + 13 * 16 + 4, idt_gate_saved[4]);
                    idt_gate_modified = 0;
                }
                if (ss_gate_modified) {
                    kernel_setchar(idt_access + 12 * 16 + 4, ss_gate_saved[4]);
                    ss_gate_modified = 0;
                }
                /* Restore SIGBUS */
                if (sigbus_installed) {
                    sigaction(SIGBUS, &old_sigbus_act, NULL);
                    sigbus_installed = 0;
                }
                /* Restore SIGSEGV */
                if (sigsegv_installed) {
                    sigaction(SIGSEGV, &old_sigsegv_act, NULL);
                    sigsegv_installed = 0;
                }
                /* Restore sigaltstack */
                if (had_old_sigalt) {
                    sigaltstack(&old_sigalt, NULL);
                    had_old_sigalt = 0;
                }
                /* Unpin CPU */
                if (cpu_pinned) {
                    cpuset_t all;
                    CPU_ZERO(&all);
                    for (int i = 0; i < 16; i++)
                        CPU_SET(i, &all);
                    cpuset_setaffinity(CPU_LEVEL_WHICH, CPU_WHICH_PID, getpid(),
                                       sizeof(all), &all);
                    pthread_setaffinity_np(pthread_self(), sizeof(all), &all);
                    cpu_pinned = 0;
                }
                /* Free pages */
                if (sigalt_stack) {
                    munmap(sigalt_stack, 64 * 1024);
                    sigalt_stack = NULL;
                }
                if (ist_page) {
                    munmap(ist_page, 4096);
                    ist_page = NULL;
                }

                send_response(sock, "OK\n");
                return;
            } else {
                send_response(sock,
                    "  mc_rip=0x%lx is outside kernel .text range, discarding\n",
                    addr);
            }
        } else {
            send_response(sock, "  No result after %d attempts\n",
                          (int)gp_trap_attempt_count);
            if (gp_trap_sig_received > 0)
                send_response(sock, "  Last signal received: %d (%s)\n",
                              (int)gp_trap_sig_received,
                              gp_trap_sig_received == SIGBUS ? "SIGBUS" :
                              gp_trap_sig_received == SIGSEGV ? "SIGSEGV" : "?");
            else
                send_response(sock, "  No signal received\n");

            /* Dump final IST page state for diagnostics */
            if (ist_page) {
                volatile uint8_t *istp2 = (volatile uint8_t *)ist_page;
                send_response(sock,
                    "  Final IST frame: err=%lx RIP=%lx CS=%lx "
                    "FL=%lx RSP=%lx SS=%lx\n",
                    *(volatile uint64_t *)(istp2 + 0xFD0),
                    *(volatile uint64_t *)(istp2 + 0xFD8),
                    *(volatile uint64_t *)(istp2 + 0xFE0),
                    *(volatile uint64_t *)(istp2 + 0xFE8),
                    *(volatile uint64_t *)(istp2 + 0xFF0),
                    *(volatile uint64_t *)(istp2 + 0xFF8));
            }
        }

    step7_cleanup:
        send_response(sock, "\nStep 7 cleanup...\n");

        /* Stop writer thread */
        gp_trap_stop_writer = 1;
        if (writer_started) {
            thrd_join(writer_thread, NULL);
            writer_started = 0;
        }

        /* Restore per-CPU TSS IST entries */
        for (int cpu = 0; cpu < GP_TRAP_MAX_CPUS; cpu++) {
            for (int i = 0; i < 7; i++) {
                if (ist_modified_percpu[cpu][i]) {
                    uint64_t cpu_tss = tss_va + (uint64_t)cpu * tss_stride;
                    kernel_setlong(cpu_tss + 0x24 + i * 8,
                                   ist_saved_percpu[cpu][i]);
                    if (cpu == 0) /* only log CPU0 to avoid spam */
                        send_response(sock, "  Restored CPU%d IST%d to 0x%lx\n",
                                      cpu, i + 1, ist_saved_percpu[cpu][i]);
                }
            }
        }

        /* Restore IDT gates */
        if (idt_gate_modified) {
            kernel_setchar(idt_access + 13 * 16 + 4, idt_gate_saved[4]);
            send_response(sock, "  Restored #GP gate IST byte\n");
        }
        if (ss_gate_modified) {
            kernel_setchar(idt_access + 12 * 16 + 4, ss_gate_saved[4]);
            send_response(sock, "  Restored #SS gate IST byte\n");
        }

        /* Restore SIGBUS handler */
        if (sigbus_installed)
            sigaction(SIGBUS, &old_sigbus_act, NULL);

        /* Restore SIGSEGV handler */
        if (sigsegv_installed)
            sigaction(SIGSEGV, &old_sigsegv_act, NULL);

        /* Restore sigaltstack */
        if (had_old_sigalt)
            sigaltstack(&old_sigalt, NULL);

        /* Unpin CPU */
        if (cpu_pinned) {
            cpuset_t all;
            CPU_ZERO(&all);
            for (int i = 0; i < 16; i++)
                CPU_SET(i, &all);
            cpuset_setaffinity(CPU_LEVEL_WHICH, CPU_WHICH_PID, getpid(),
                               sizeof(all), &all);
            pthread_setaffinity_np(pthread_self(), sizeof(all), &all);
        }

        /* Free pages */
        if (sigalt_stack)
            munmap(sigalt_stack, 64 * 1024);
        if (ist_page)
            munmap(ist_page, 4096);

        send_response(sock, "Step 7 cleanup complete\n");
    }
    } /* end have_strong_candidate check */

    /* ---- Step 8: Classification ---- */
classify:
    send_response(sock, "\n--- Step 8: doreti_iret Candidates ---\n");

    if (num_candidates == 0) {
        send_response(sock, "No iretq candidates found.\n");
        send_response(sock, "All kernel .text pages may be HV-protected (XOM via DMAP).\n");
        send_response(sock, "OK\n");
        return;
    }

    send_response(sock, "%-3s %-16s %-14s %-7s %-8s %-6s %s\n",
                  "#", "PA", "ktext+offset", "swapgs", "near", "dist", "class");
    send_response(sock, "--- ---------------- -------------- ------- -------- ------ --------\n");

    int likely_count = 0, possible_count = 0, other_count = 0;
    int best_idx = -1;
    int best_score = -1;

    for (int c = 0; c < num_candidates; c++) {
        const char *classification;
        int score = 0;

        int near_gp = (candidates[c].near_handler == 13 && candidates[c].page_dist <= 16);
        int has_sg = candidates[c].has_swapgs_before;

        if (has_sg && near_gp) {
            classification = "LIKELY";
            score = 3;
            likely_count++;
        } else if (has_sg || near_gp) {
            classification = "POSSIBLE";
            score = 2;
            possible_count++;
        } else {
            classification = "other";
            score = 1;
            other_count++;
        }

        /* Prefer LIKELY with smallest distance to #GP handler */
        if (score > best_score ||
            (score == best_score && near_gp && candidates[c].page_dist < candidates[best_idx].page_dist)) {
            best_score = score;
            best_idx = c;
        }

        /* Show LIKELY and POSSIBLE always, limit OTHER output */
        if (score >= 2 || other_count <= 10) {
            char near_str[16];
            if (candidates[c].near_handler > 0)
                snprintf(near_str, sizeof(near_str), "vec %d", candidates[c].near_handler);
            else
                snprintf(near_str, sizeof(near_str), "-");

            send_response(sock, "%-3d 0x%014lx ktext+0x%-6lx %-7s %-8s %+dpg   %s\n",
                          c + 1,
                          candidates[c].paddr,
                          candidates[c].ktext_offset,
                          has_sg ? "YES" : "NO",
                          near_str,
                          candidates[c].page_dist,
                          classification);
        }
    }

    if (other_count > 10)
        send_response(sock, "... (%d more 'other' iretq entries omitted)\n", other_count - 10);

    /* Summary */
    send_response(sock, "\n--- Summary ---\n");
    send_response(sock, "Total iretq found: %d\n", num_candidates);
    send_response(sock, "  LIKELY doreti_iret: %d\n", likely_count);
    send_response(sock, "  POSSIBLE:          %d\n", possible_count);
    send_response(sock, "  Other iretq:       %d\n", other_count);

    if (best_idx >= 0 && best_score >= 2) {
        send_response(sock, "\nBest candidate: PA 0x%lx (est ktext+0x%lx)\n",
                      candidates[best_idx].paddr,
                      candidates[best_idx].ktext_offset);
        send_response(sock, "  swapgs before iretq: %s\n",
                      candidates[best_idx].has_swapgs_before ? "YES" : "NO");
        if (candidates[best_idx].near_handler > 0)
            send_response(sock, "  near handler: vec %d (%+d pages)\n",
                          candidates[best_idx].near_handler,
                          candidates[best_idx].page_dist);
    } else {
        send_response(sock, "\nNo strong doreti_iret candidate found.\n");
    }

    send_response(sock, "\nNotes:\n");
    send_response(sock, "  doreti_iret is the iretq in the interrupt return path\n");
    send_response(sock, "  #GP handler references it for fault-on-iret detection\n");
    send_response(sock, "  Phase 7c will redirect #DB to singlestep through this instruction\n");
    send_response(sock, "OK\n");

    #undef MAX_DORETI_CANDIDATES
}

/* Display kernel information */
static void
cmd_kinfo(int sock) {
    intptr_t kdata_base = KERNEL_ADDRESS_DATA_BASE;
    intptr_t ktext_base = KERNEL_ADDRESS_TEXT_BASE;
    uint32_t fw_version = kernel_get_fw_version();

    /* Read kernel info */
    intptr_t pmap_store = kdata_base + PMAP_STORE_OFFSET;
    uint64_t pm_cr3 = get_kernel_cr3();
    uint64_t dmap_base = get_dmap_base();

    send_response(sock, "=== PS5 Kernel Information ===\n");
    send_response(sock, "Firmware:        0x%08x (%d.%02d)\n",
                  fw_version,
                  (fw_version >> 24) & 0xFF,
                  (fw_version >> 16) & 0xFF);
    send_response(sock, "Kernel .text:    0x%lx\n", ktext_base);
    send_response(sock, "Kernel .data:    0x%lx\n", kdata_base);
    send_response(sock, "\n=== PMAP Information ===\n");
    send_response(sock, "pmap_store:      0x%lx\n", pmap_store);
    send_response(sock, "pmap_offset:     0x%x\n", PMAP_STORE_OFFSET);
    send_response(sock, "Kernel CR3:      0x%lx (KPML4phys @ kdata+0x%x)\n", pm_cr3, KERNEL_CR3_OFFSET);
    send_response(sock, "DMAP base:       0x%lx\n", dmap_base);
    send_response(sock, "\n=== Security Flags ===\n");
    send_response(sock, "TARGETID:        0x%02x\n", kernel_getchar(KERNEL_ADDRESS_TARGETID));
    send_response(sock, "SECURITY_FLAGS:  0x%02x\n", kernel_getchar(KERNEL_ADDRESS_SECURITY_FLAGS));
    send_response(sock, "UTOKEN_FLAGS:    0x%02x\n", kernel_getchar(KERNEL_ADDRESS_UTOKEN_FLAGS));
    send_response(sock, "OK\n");
}

/* Dump from kernel .data base */
static void
cmd_dump_base(int sock) {
    intptr_t kdata_base = KERNEL_ADDRESS_DATA_BASE;
    size_t dump_size = 0x100000; /* 1MB */

    send_response(sock, "Dumping 1MB from kernel .data base (0x%lx)...\n", kdata_base);
    dump_memory(sock, kdata_base, dump_size);
}

/* Dump from virtual address */
static void
cmd_dump_vaddr(int sock, const char *args) {
    unsigned long addr;
    unsigned long size;

    if (sscanf(args, "%lx %lx", &addr, &size) != 2) {
        send_response(sock, "ERROR: Usage: dump_vaddr <addr> <size>\n");
        return;
    }

    if (size > 0x10000000) { /* 256MB max */
        send_response(sock, "ERROR: Size too large (max 256MB)\n");
        return;
    }

    send_response(sock, "Dumping 0x%lx bytes from vaddr 0x%lx...\n", size, addr);
    dump_memory(sock, (intptr_t)addr, (size_t)size);
}

/* Dump from physical address via DMAP */
static void
cmd_dump_paddr(int sock, const char *args) {
    unsigned long paddr;
    unsigned long size;

    if (sscanf(args, "%lx %lx", &paddr, &size) != 2) {
        send_response(sock, "ERROR: Usage: dump_paddr <paddr> <size>\n");
        return;
    }

    if (size > 0x10000000) { /* 256MB max */
        send_response(sock, "ERROR: Size too large (max 256MB)\n");
        return;
    }

    /* Get DMAP base */
    uint64_t dmap_base = get_dmap_base();

    if (dmap_base == 0) {
        send_response(sock, "ERROR: Failed to get DMAP base\n");
        return;
    }

    intptr_t vaddr = dmap_base + paddr;

    send_response(sock, "Dumping 0x%lx bytes from paddr 0x%lx (DMAP vaddr 0x%lx)...\n",
                  size, paddr, vaddr);
    dump_memory(sock, vaddr, (size_t)size);
}

/* Parse and handle client command */
static int
handle_command(int sock, char *cmd) {
    /* Trim newline */
    char *nl = strchr(cmd, '\n');
    if (nl) *nl = '\0';
    nl = strchr(cmd, '\r');
    if (nl) *nl = '\0';

    if (strlen(cmd) == 0) {
        return 0;
    }

    if (strcmp(cmd, "kinfo") == 0) {
        cmd_kinfo(sock);
    } else if (strcmp(cmd, "dump_base") == 0) {
        cmd_dump_base(sock);
    } else if (strncmp(cmd, "dump_vaddr ", 11) == 0) {
        cmd_dump_vaddr(sock, cmd + 11);
    } else if (strncmp(cmd, "dump_paddr ", 11) == 0) {
        cmd_dump_paddr(sock, cmd + 11);
    } else if (strncmp(cmd, "dump_pte ", 9) == 0) {
        cmd_dump_pte(sock, cmd + 9);
    } else if (strncmp(cmd, "scan_pte ", 9) == 0) {
        cmd_scan_pte(sock, cmd + 9);
    } else if (strcmp(cmd, "cmp_sections") == 0) {
        cmd_cmp_sections(sock);
    } else if (strcmp(cmd, "probe_xom") == 0) {
        cmd_probe_xom(sock);
    } else if (strcmp(cmd, "dump_pmap") == 0) {
        cmd_dump_pmap(sock);
    } else if (strcmp(cmd, "find_kcr3") == 0) {
        cmd_find_kcr3(sock);
    /* HV Bypass Research Commands */
    } else if (strcmp(cmd, "cpuid_info") == 0) {
        cmd_cpuid_info(sock);
    } else if (strncmp(cmd, "scan_rwx ", 9) == 0) {
        cmd_scan_rwx(sock, cmd + 9);
    } else if (strcmp(cmd, "scan_code_sig") == 0) {
        cmd_scan_code_sig(sock, "");
    } else if (strncmp(cmd, "scan_code_sig ", 14) == 0) {
        cmd_scan_code_sig(sock, cmd + 14);
    } else if (strcmp(cmd, "msr_dump") == 0) {
        cmd_msr_dump(sock);
    } else if (strncmp(cmd, "probe_dmap ", 11) == 0) {
        cmd_probe_dmap(sock, cmd + 11);
    } else if (strcmp(cmd, "apic_probe") == 0) {
        cmd_apic_probe(sock);
    } else if (strcmp(cmd, "apic_timing") == 0) {
        cmd_apic_timing(sock);
    } else if (strcmp(cmd, "map_xom_boundary") == 0) {
        cmd_map_xom_boundary(sock, "");
    } else if (strncmp(cmd, "map_xom_boundary ", 17) == 0) {
        cmd_map_xom_boundary(sock, cmd + 17);
    } else if (strncmp(cmd, "timing_probe ", 13) == 0) {
        cmd_timing_probe(sock, cmd + 13);
    } else if (strcmp(cmd, "timing_boundary") == 0) {
        cmd_timing_boundary(sock);
    } else if (strcmp(cmd, "verify_xom") == 0) {
        cmd_verify_xom(sock);
    } else if (strcmp(cmd, "scan_apic_ops") == 0) {
        cmd_scan_apic_ops(sock, "");
    } else if (strncmp(cmd, "scan_apic_ops ", 14) == 0) {
        cmd_scan_apic_ops(sock, cmd + 14);
    } else if (strncmp(cmd, "identify_table ", 15) == 0) {
        cmd_identify_table(sock, cmd + 15);
    } else if (strncmp(cmd, "analyze_apic_ops ", 17) == 0) {
        cmd_analyze_apic_ops(sock, cmd + 17);
    } else if (strcmp(cmd, "find_cfi_targets") == 0) {
        cmd_find_cfi_targets(sock);
    } else if (strcmp(cmd, "idt_diag") == 0) {
        cmd_idt_diag(sock);
    } else if (strcmp(cmd, "dump_idt") == 0) {
        cmd_dump_idt(sock);
    } else if (strcmp(cmd, "find_doreti_iret") == 0) {
        cmd_find_doreti_iret(sock, NULL);
    } else if (strncmp(cmd, "find_doreti_iret ", 17) == 0) {
        cmd_find_doreti_iret(sock, cmd + 17);
    } else if (strcmp(cmd, "exit") == 0 || strcmp(cmd, "quit") == 0) {
        send_response(sock, "Goodbye!\n");
        return -1;
    } else if (strcmp(cmd, "help") == 0) {
        send_response(sock, "=== meme_dumper commands ===\n");
        send_response(sock, "kinfo                    - Show kernel information\n");
        send_response(sock, "dump_base                - Dump 1MB from kernel .data\n");
        send_response(sock, "dump_vaddr <addr> <size> - Dump from virtual address\n");
        send_response(sock, "dump_paddr <addr> <size> - Dump from physical address via DMAP\n");
        send_response(sock, "dump_pte <vaddr>         - Walk page tables for address\n");
        send_response(sock, "scan_pte <va> <n> [s]    - Scan PTEs for address range\n");
        send_response(sock, "cmp_sections             - Compare .text vs .data mappings\n");
        send_response(sock, "find_kcr3                - Search for kernel CR3/PML4\n");
        send_response(sock, "probe_xom                - Analyze XOM protection (safe)\n");
        send_response(sock, "dump_pmap                - Debug: dump raw pmap_store\n");
        send_response(sock, "\n=== HV Bypass Research ===\n");
        send_response(sock, "cpuid_info               - CPU/HV feature detection\n");
        send_response(sock, "scan_rwx <start> <end>   - Find RWX pages\n");
        send_response(sock, "scan_code_sig [pa] [sz]  - Search for code patterns\n");
        send_response(sock, "msr_dump                 - Find cached MSR values\n");
        send_response(sock, "probe_dmap <start> <end> - Fault-safe DMAP probe\n");
        send_response(sock, "apic_probe               - APIC register analysis\n");
        send_response(sock, "apic_timing              - Measure memory access timing\n");
        send_response(sock, "map_xom_boundary [s] [e] - Find XOM region boundaries\n");
        send_response(sock, "timing_probe <pa> [n]    - Time reads at PA (n samples)\n");
        send_response(sock, "timing_boundary          - Time reads at XOM boundary\n");
        send_response(sock, "verify_xom               - Verify XOM boundaries + APIC state\n");
        send_response(sock, "scan_apic_ops [min]      - Find function pointer tables\n");
        send_response(sock, "identify_table <off> [ctx] - Identify func ptr table (kdata offset)\n");
        send_response(sock, "analyze_apic_ops <off>   - Full apic_ops analysis (36 entries)\n");
        send_response(sock, "find_cfi_targets         - Find CFI-valid function targets\n");
        send_response(sock, "idt_diag                 - IDT diagnostic (relaxed gate scan, 64MB)\n");
        send_response(sock, "dump_idt                 - Dump IDT (handlers, IST, types)\n");
        send_response(sock, "find_doreti_iret [off]   - Find doreti_iret (or use known ktext offset)\n");
        send_response(sock, "\nexit                     - Close connection\n");
        send_response(sock, "help                     - Show this help\n");
    } else {
        send_response(sock, "ERROR: Unknown command '%s'. Type 'help' for commands.\n", cmd);
    }

    return 0;
}

/* Handle client connection */
static void
handle_client(int client_sock) {
    char buf[BUFFER_SIZE];
    ssize_t len;

    send_response(client_sock, "=== meme_dumper for PS5 ===\n");
    send_response(client_sock, "Type 'help' for commands\n");
    send_response(client_sock, "> ");

    while ((len = recv(client_sock, buf, sizeof(buf) - 1, 0)) > 0) {
        buf[len] = '\0';

        if (handle_command(client_sock, buf) < 0) {
            break;
        }

        send_response(client_sock, "> ");
    }
}

int
main(void) {
    int server_sock, client_sock;
    struct sockaddr_in server_addr, client_addr;
    socklen_t client_len = sizeof(client_addr);
    int opt = 1;

    notify("meme_dumper starting...");

    /* Create socket */
    server_sock = socket(AF_INET, SOCK_STREAM, 0);
    if (server_sock < 0) {
        notify("Failed to create socket");
        return 1;
    }

    /* Set socket options */
    setsockopt(server_sock, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));

    /* Bind to port */
    memset(&server_addr, 0, sizeof(server_addr));
    server_addr.sin_family = AF_INET;
    server_addr.sin_addr.s_addr = INADDR_ANY;
    server_addr.sin_port = htons(SERVER_PORT);

    if (bind(server_sock, (struct sockaddr *)&server_addr, sizeof(server_addr)) < 0) {
        notify("Failed to bind socket");
        close(server_sock);
        return 1;
    }

    /* Listen for connections */
    if (listen(server_sock, 1) < 0) {
        notify("Failed to listen");
        close(server_sock);
        return 1;
    }

    notify("meme_dumper listening on port 9023");
    printf("meme_dumper: Listening on port %d\n", SERVER_PORT);
    printf("meme_dumper: Kernel .data base: 0x%lx\n", (unsigned long)KERNEL_ADDRESS_DATA_BASE);
    printf("meme_dumper: Kernel .text base: 0x%lx\n", (unsigned long)KERNEL_ADDRESS_TEXT_BASE);

    /* Accept and handle connections */
    while (1) {
        client_sock = accept(server_sock, (struct sockaddr *)&client_addr, &client_len);
        if (client_sock < 0) {
            continue;
        }

        printf("meme_dumper: Client connected from %s\n",
               inet_ntoa(client_addr.sin_addr));

        handle_client(client_sock);

        close(client_sock);
        printf("meme_dumper: Client disconnected\n");
    }

    close(server_sock);
    return 0;
}
