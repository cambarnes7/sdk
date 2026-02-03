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
 *   exit        - Close connection
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
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
#define PMAP_OFFSET_DMAP_BASE  0x278

/* pmap_store offset from kernel data base - FW 4.03 */
#define PMAP_STORE_OFFSET      0x3257a78

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

/* Display kernel information */
static void
cmd_kinfo(int sock) {
    intptr_t kdata_base = KERNEL_ADDRESS_DATA_BASE;
    intptr_t ktext_base = KERNEL_ADDRESS_TEXT_BASE;
    uint32_t fw_version = kernel_get_fw_version();

    /* Read pmap_store structure */
    intptr_t pmap_store = kdata_base + PMAP_STORE_OFFSET;

    uint64_t pm_pml4 = kernel_getlong(pmap_store + PMAP_OFFSET_PM_PML4);
    uint64_t pm_cr3 = kernel_getlong(pmap_store + PMAP_OFFSET_PM_CR3);
    uint64_t dmap_base = kernel_getlong(pmap_store + PMAP_OFFSET_DMAP_BASE);

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
    send_response(sock, "pm_pml4:         0x%lx\n", pm_pml4);
    send_response(sock, "pm_cr3:          0x%lx\n", pm_cr3);
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

    /* Get DMAP base from pmap_store */
    intptr_t kdata_base = KERNEL_ADDRESS_DATA_BASE;
    intptr_t pmap_store = kdata_base + PMAP_STORE_OFFSET;
    uint64_t dmap_base = kernel_getlong(pmap_store + PMAP_OFFSET_DMAP_BASE);

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
    } else if (strcmp(cmd, "exit") == 0 || strcmp(cmd, "quit") == 0) {
        send_response(sock, "Goodbye!\n");
        return -1;
    } else if (strcmp(cmd, "help") == 0) {
        send_response(sock, "=== meme_dumper commands ===\n");
        send_response(sock, "kinfo                    - Show kernel information\n");
        send_response(sock, "dump_base                - Dump 1MB from kernel .data\n");
        send_response(sock, "dump_vaddr <addr> <size> - Dump from virtual address\n");
        send_response(sock, "dump_paddr <addr> <size> - Dump from physical address via DMAP\n");
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
