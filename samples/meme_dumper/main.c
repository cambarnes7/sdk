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
 *   exit        - Close connection
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <unistd.h>
#include <errno.h>

#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

#include <ps5/kernel.h>

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
#define NBPDR               (1UL << PDRSHIFT)   /* 2MB */
#define NBPDP               (1UL << PDPSHIFT)   /* 1GB */

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
 * probe_xom - Diagnose XOM enforcement level
 */
static void
cmd_probe_xom(int sock)
{
    intptr_t ktext_base = KERNEL_ADDRESS_TEXT_BASE;
    uint64_t text_paddr = 0, text_flags = 0;

    uint64_t pm_cr3 = get_kernel_cr3();
    uint64_t dmap_base = get_dmap_base();

    send_response(sock, "=== XOM Probe Analysis ===\n\n");

    /* Get physical address of kernel .text */
    send_response(sock, "Step 1: Walking page tables for kernel .text...\n");
    if (vaddr_to_paddr(sock, ktext_base, dmap_base, pm_cr3, &text_paddr, &text_flags) != 0) {
        send_response(sock, "ERROR: Cannot translate kernel .text address\n");
        return;
    }

    send_response(sock, "\nStep 2: Testing different access methods...\n\n");

    uint8_t sample_direct[32], sample_dmap[32];
    int direct_ok = 0, dmap_ok = 0;

    /* Method 1: Direct read via kernel vaddr */
    send_response(sock, "Method 1 - Direct kernel_copyout(0x%lx):\n", ktext_base);
    memset(sample_direct, 0, sizeof(sample_direct));
    if (kernel_copyout(ktext_base, sample_direct, 32) == 0) {
        direct_ok = 1;
        send_response(sock, "  SUCCESS: ");
        for (int i = 0; i < 16; i++)
            send_response(sock, "%02x ", sample_direct[i]);
        send_response(sock, "\n");
    } else {
        send_response(sock, "  FAILED\n");
    }

    /* Method 2: Read via DMAP using translated physical address */
    uint64_t dmap_vaddr = dmap_base + text_paddr;
    send_response(sock, "\nMethod 2 - DMAP read(0x%lx) [PA 0x%lx]:\n", dmap_vaddr, text_paddr);
    memset(sample_dmap, 0, sizeof(sample_dmap));
    if (kernel_copyout(dmap_vaddr, sample_dmap, 32) == 0) {
        dmap_ok = 1;
        send_response(sock, "  SUCCESS: ");
        for (int i = 0; i < 16; i++)
            send_response(sock, "%02x ", sample_dmap[i]);
        send_response(sock, "\n");
    } else {
        send_response(sock, "  FAILED\n");
    }

    /* Analysis */
    send_response(sock, "\n=== Diagnosis ===\n");
    if (!direct_ok && !dmap_ok) {
        send_response(sock, "Both methods failed - likely HV-enforced XOM\n");
        send_response(sock, "The hypervisor may be intercepting ALL reads to code pages\n");
    } else if (direct_ok && dmap_ok) {
        if (memcmp(sample_direct, sample_dmap, 32) == 0) {
            send_response(sock, "Both methods return SAME data\n");
        } else {
            send_response(sock, "Methods return DIFFERENT data!\n");
            send_response(sock, "DMAP may be returning shadow/fake data (HV interception)\n");
        }
    } else if (direct_ok && !dmap_ok) {
        send_response(sock, "Direct works but DMAP fails - unusual configuration\n");
    } else {
        send_response(sock, "DMAP works but direct fails - possible kernel-level XOM\n");
    }

    /* Check for vtable signatures */
    send_response(sock, "\n=== Content Analysis ===\n");
    int has_kernel_ptrs = 0;
    uint8_t *sample = dmap_ok ? sample_dmap : sample_direct;
    for (int i = 0; i < 4; i++) {
        uint64_t val;
        memcpy(&val, sample + (i * 8), 8);
        /* Check for kernel pointer ranges: 0xffffffff8xxxxxxx or 0xffffffffcxxxxxxx */
        if ((val >> 32) == 0xffffffff && ((val >> 28) & 0xF) >= 0x8) {
            has_kernel_ptrs++;
        }
    }

    if (has_kernel_ptrs >= 2) {
        send_response(sock, "Data contains multiple kernel pointers\n");
        send_response(sock, "This looks like VTABLES, NOT executable code!\n");
        send_response(sock, "Possible causes:\n");
        send_response(sock, "  1. KERNEL_ADDRESS_TEXT_BASE is incorrect\n");
        send_response(sock, "  2. HV is returning different data for code pages\n");
    } else {
        /* Check for x86-64 code patterns */
        int has_prologue = 0;
        for (int i = 0; i < 28; i++) {
            if (sample[i] == 0x55 && sample[i+1] == 0x48 &&
                sample[i+2] == 0x89 && sample[i+3] == 0xe5) {
                has_prologue = 1;
                break;
            }
        }
        if (has_prologue) {
            send_response(sock, "Found x86-64 function prologue (push rbp; mov rbp,rsp)\n");
            send_response(sock, "This appears to be ACTUAL CODE!\n");
        } else {
            send_response(sock, "No obvious code patterns or vtables detected\n");
            send_response(sock, "Data may be encrypted or this is a different region\n");
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
        send_response(sock, "probe_xom                - Analyze XOM protection mechanism\n");
        send_response(sock, "dump_pmap                - Debug: dump raw pmap_store structure\n");
        send_response(sock, "exit                     - Close connection\n");
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
