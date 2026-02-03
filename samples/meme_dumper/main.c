/* Copyright (C) 2024 cheburek3000
   Ported to ps5-payload-sdk

This program is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation; either version 2, or (at your option) any
later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; see the file COPYING. If not, see
<http://www.gnu.org/licenses/>.  */

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

#include <ps5/kernel.h>

#define PC_IP "192.168.1.100"
#define PC_LOG_PORT 5655

#define DUMP_SERVER_PORT 9081

enum Errors {
	ERR_LOG_SOCK = 1,
	ERR_LOG_CONNECT,
	ERR_PMAP_OFFSET_GUESS,
	ERR_DUMPER_BUF_MALLOC,
	ERR_DUMPER_SOCK,
	ERR_DUMPER_SETSOCKOPT,
	ERR_DUMPER_BIND,
	ERR_DUMPER_LISTEN,
	ERR_DUMPER_CMD_READ,
	ERR_DUMP_COPYOUT,
	ERR_DUMP_WRITE,
	ERR_PADDR_NEGATIVE,
	ERR_VADDR_NOT_PRESENT,
	ERR_VADDR_NO_LEAF,
};

static int err_to_return(int value) {
	return (value << 16) + errno;
}

static const char CMD_DUMP_ABS[] = "dump_abs";
static const char CMD_DUMP_BASE[] = "dump_base";
static const char CMD_DUMP_VADDR[] = "dump_vaddr";
static const char CMD_DUMP_PADDR[] = "dump_paddr";
static const char CMD_DUMP_RANGES[] = "dump_ranges";
static const char CMD_STOP[] = "stop";

#define CMD_IS(x) \
	(cmd_sz >= (sizeof(x) - 1) && memcmp((x), cmd_buf, (sizeof(x) - 1)) == 0)

static const size_t CMD_BUF_SIZE = 0x100;
static const size_t DUMP_BUF_SIZE = 0x100000;

static void sock_print(int sock, char *str) {
	size_t size = strlen(str);
	write(sock, str, size);
}

static int write_buf(int sock, char *buf, size_t size) {
	size_t written = 0;
	while (written < size) {
		ssize_t ret = write(sock, buf + written, size - written);
		if (ret < 0) {
			return -1;
		}
		written += ret;
	}
	return 0;
}

struct flat_pmap {
	uint64_t mtx_name_ptr;
	uint64_t mtx_flags;
	uint64_t mtx_data;
	uint64_t mtx_lock;
	uint64_t pm_pml4;
	uint64_t pm_cr3;
};

static ssize_t guess_kernel_pmap_store_offset(intptr_t kdata_base) {
	char *kdata;
	ssize_t result = -1;
	ssize_t offset;
	struct flat_pmap pmap;

	kdata = malloc(DUMP_BUF_SIZE);
	if (kdata == NULL) {
		result = -ERR_DUMPER_BUF_MALLOC;
		goto guess_offset_out;
	}
	for (offset = 0; offset + sizeof(struct flat_pmap) < 0x4000000; ++offset) {
		if ((offset % DUMP_BUF_SIZE) == 0) {
			kernel_copyout(kdata_base + offset, kdata, DUMP_BUF_SIZE);
		}
		memcpy(&pmap, kdata + (offset % DUMP_BUF_SIZE), sizeof(pmap));
		if (pmap.mtx_flags == 0x1430000 && pmap.mtx_data == 0x0 &&
		    pmap.mtx_lock == 0x4 && pmap.pm_pml4 != 0 &&
		    (pmap.pm_pml4 & 0xFFFFFFFFULL) == pmap.pm_cr3) {
			result = offset;
		}
	}
guess_offset_out:
	if (kdata != NULL) {
		free(kdata);
	}
	return result;
}

struct page_level {
	int from;
	int to;
	size_t size;
	int sign_ext;
	int leaf;
};

static const struct page_level LEVELS[] = {
	{.from = 39, .to = 47, .size = 1ULL << 39, .sign_ext = 1, .leaf = 0},
	{.from = 30, .to = 38, .size = 1ULL << 30, .sign_ext = 0, .leaf = 0},
	{.from = 21, .to = 29, .size = 1ULL << 21, .sign_ext = 0, .leaf = 0},
	{.from = 12, .to = 20, .size = 1ULL << 12, .sign_ext = 0, .leaf = 1},
};

enum pde_shift {
	PDE_PRESENT = 0,
	PDE_RW,
	PDE_USER,
	PDE_WRITE_THROUGH,
	PDE_CACHE_DISABLE,
	PDE_ACCESSED,
	PDE_DIRTY,
	PDE_PS,
	PDE_GLOBAL,
	PDE_PROTECTION_KEY = 59,
	PDE_EXECUTE_DISABLE = 63
};

static const size_t PDE_PRESENT_MASK = 1;
static const size_t PDE_RW_MASK = 1;
static const size_t PDE_USER_MASK = 1;
static const size_t PDE_WRITE_THROUGH_MASK = 1;
static const size_t PDE_CACHE_DISABLE_MASK = 1;
static const size_t PDE_ACCESSED_MASK = 1;
static const size_t PDE_DIRTY_MASK = 1;
static const size_t PDE_PS_MASK = 1;
static const size_t PDE_GLOBAL_MASK = 1;
static const size_t PDE_PROTECTION_KEY_MASK = 0xF;
static const size_t PDE_EXECUTE_DISABLE_MASK = 1;

#define PDE_FIELD(pde, name) (((pde) >> PDE_##name) & PDE_##name##_MASK)

static const size_t PDE_ADDR_MASK = 0xffffffffff800ULL;

#define PADDR_TO_DMAP(paddr, dmap_base) ((paddr) + (dmap_base))

static ssize_t vaddr_to_paddr(size_t vaddr, size_t dmap_base, size_t cr3,
                              size_t *page_end, int log_sock) {
	ssize_t paddr = cr3;
	uint64_t pd[512];
	const struct page_level *level;

	for (size_t level_idx = 0; level_idx < 4; ++level_idx) {
		level = LEVELS + level_idx;
		if (paddr < 0) {
			return -ERR_PADDR_NEGATIVE;
		}
		kernel_copyout(PADDR_TO_DMAP(paddr, dmap_base), &pd, sizeof(pd));
		int idx_bits = (level->to - level->from) + 1;
		size_t idx_mask = (1ULL << idx_bits) - 1ULL;
		size_t idx = (vaddr >> level->from) & idx_mask;

		uint64_t pde = pd[idx];
		paddr = pde & PDE_ADDR_MASK;
		size_t leaf = level->leaf || PDE_FIELD(pde, PS);

		if (!PDE_FIELD(pde, PRESENT)) {
			return -ERR_VADDR_NOT_PRESENT;
		}

		if (leaf) {
			*page_end = paddr + level->size;
			return paddr | (vaddr & (level->size - 1));
		}
	}
	return -ERR_VADDR_NO_LEAF;
}

struct vaddr_paddr_range {
	size_t vaddr_begin, vaddr_end;
	size_t paddr_begin, paddr_end;
	size_t pte_flags;
};

struct vaddr_paddr_ranges {
	struct vaddr_paddr_range *ranges;
	size_t len;
	size_t cap;
};

static const size_t PTE_FLAGS_MASK =
    (PDE_RW_MASK << PDE_RW) |
    (PDE_USER_MASK << PDE_USER) |
    (PDE_WRITE_THROUGH_MASK << PDE_WRITE_THROUGH) |
    (PDE_CACHE_DISABLE_MASK << PDE_CACHE_DISABLE) |
    (PDE_GLOBAL_MASK << PDE_GLOBAL) |
    (PDE_EXECUTE_DISABLE_MASK << PDE_EXECUTE_DISABLE) |
    (PDE_PROTECTION_KEY_MASK << PDE_PROTECTION_KEY);

static ssize_t append_range(size_t vaddr, size_t paddr, size_t size, size_t pte,
                            struct vaddr_paddr_ranges *ranges) {
	if (ranges->len + 1 > ranges->cap) {
		struct vaddr_paddr_range *old_ranges = ranges->ranges;
		size_t old_cap = ranges->cap;
		ranges->cap = ranges->cap ? ranges->cap * 2 : 8096;
		ranges->ranges = malloc(ranges->cap * sizeof(struct vaddr_paddr_range));
		if (ranges->ranges == NULL) {
			if (old_ranges != NULL) {
				free(old_ranges);
			}
			return -ranges->cap;
		}
		if (old_ranges != NULL) {
			memcpy(ranges->ranges, old_ranges,
			       old_cap * sizeof(struct vaddr_paddr_range));
			free(old_ranges);
		}
	}
	struct vaddr_paddr_range new_range = {
		.vaddr_begin = vaddr,
		.vaddr_end = vaddr + size,
		.paddr_begin = paddr,
		.paddr_end = paddr + size,
		.pte_flags = pte & PTE_FLAGS_MASK
	};
	struct vaddr_paddr_range *old_range =
	    ranges->len > 0 ? &ranges->ranges[ranges->len - 1] : NULL;
	if (old_range && old_range->vaddr_end == new_range.vaddr_begin &&
	    old_range->paddr_end == new_range.paddr_begin &&
	    old_range->pte_flags == new_range.pte_flags) {
		old_range->vaddr_end = new_range.vaddr_end;
		old_range->paddr_end = new_range.paddr_end;
	} else {
		ranges->ranges[ranges->len++] = new_range;
	}
	return 0;
}

static const size_t SIGN_EXT_MASK = 0xffff000000000000;

static ssize_t collect_ranges(size_t dmap_base, size_t paddr, size_t vaddr,
                              size_t level_idx, struct vaddr_paddr_ranges *ranges) {
	ssize_t ret = 0;
	uint64_t pd[512];
	const struct page_level *level;

	level = LEVELS + level_idx;
	kernel_copyout(PADDR_TO_DMAP(paddr, dmap_base), &pd, sizeof(pd));
	for (size_t idx = 0; idx < 512; ++idx) {
		uint64_t pde = pd[idx];
		size_t next_paddr = pde & PDE_ADDR_MASK;
		size_t next_vaddr = vaddr | (idx << level->from);
		if (level->sign_ext && ((idx >> (level->to - level->from)) & 1)) {
			next_vaddr |= SIGN_EXT_MASK;
		}

		size_t leaf = level->leaf || PDE_FIELD(pde, PS);

		if (!PDE_FIELD(pde, PRESENT)) {
			continue;
		}

		if (leaf) {
			ret = append_range(next_vaddr, next_paddr, level->size, pde, ranges);
		} else {
			ret = collect_ranges(dmap_base, next_paddr, next_vaddr, level_idx + 1,
			                     ranges);
		}
		if (ret < 0) {
			return ret;
		}
	}
	return ret;
}

static void print_ranges(struct vaddr_paddr_ranges *ranges, int sock) {
	char printbuf[256];
	for (size_t i = 0; i < ranges->len; ++i) {
		struct vaddr_paddr_range *range = &ranges->ranges[i];
		size_t pde = range->pte_flags;
		sprintf(printbuf,
		        "[%p, %p) -> [%p, %p), rw %zu, x %zu, user %zu, glob %zu, pk %zu, wt %zu, cd %zu\n",
		        (void*)range->vaddr_begin, (void*)range->vaddr_end,
		        (void*)range->paddr_begin, (void*)range->paddr_end,
		        PDE_FIELD(pde, RW),
		        !PDE_FIELD(pde, EXECUTE_DISABLE), PDE_FIELD(pde, USER),
		        PDE_FIELD(pde, GLOBAL), PDE_FIELD(pde, PROTECTION_KEY),
		        PDE_FIELD(pde, WRITE_THROUGH), PDE_FIELD(pde, CACHE_DISABLE));
		sock_print(sock, printbuf);
	}
}

int main(void) {
	int exit_code = 0;
	int ret;
	int log_sock = -1, dumper_sock = -1;
	int running = 1;
	int client = 0;
	char cmd_buf[CMD_BUF_SIZE];
	char *dump_buf = NULL;
	ssize_t cmd_sz = 0;
	char printbuf[256];
	struct sockaddr_in log_addr, dumper_addr;
	intptr_t kdata_base;
	ssize_t pmap_offset = -1;
	struct flat_pmap kernel_pmap_store;
	size_t dmap_base = 0;
	struct vaddr_paddr_ranges mem_ranges = {.ranges = NULL, .cap = 0, .len = 0};

	kdata_base = KERNEL_ADDRESS_DATA_BASE;

	log_sock = socket(AF_INET, SOCK_STREAM, 0);
	if (log_sock < 0) {
		exit_code = err_to_return(ERR_LOG_SOCK);
		goto out;
	}

	memset(&log_addr, 0, sizeof(log_addr));
	inet_pton(AF_INET, PC_IP, &log_addr.sin_addr);
	log_addr.sin_family = AF_INET;
	log_addr.sin_port = htons(PC_LOG_PORT);

	ret = connect(log_sock, (const struct sockaddr *)&log_addr, sizeof(log_addr));
	if (ret < 0) {
		exit_code = err_to_return(ERR_LOG_CONNECT);
		goto out;
	}

	dumper_sock = socket(AF_INET, SOCK_STREAM, 0);
	if (dumper_sock < 0) {
		exit_code = err_to_return(ERR_DUMPER_SOCK);
		goto out;
	}

	const int enable = 1;
	ret = setsockopt(dumper_sock, SOL_SOCKET, SO_REUSEADDR, &enable, sizeof(int));
	if (ret < 0) {
		exit_code = err_to_return(ERR_DUMPER_SETSOCKOPT);
		goto out;
	}

	memset(&dumper_addr, 0, sizeof(dumper_addr));
	dumper_addr.sin_family = AF_INET;
	dumper_addr.sin_port = htons(DUMP_SERVER_PORT);
	dumper_addr.sin_addr.s_addr = INADDR_ANY;

	ret = bind(dumper_sock, (const struct sockaddr *)&dumper_addr,
	           sizeof(dumper_addr));
	if (ret < 0) {
		exit_code = err_to_return(ERR_DUMPER_BIND);
		goto out;
	}

	ret = listen(dumper_sock, 5);
	if (ret < 0) {
		exit_code = err_to_return(ERR_DUMPER_LISTEN);
		goto out;
	}

	sprintf(printbuf, "[+] meme_dumper started\n");
	sock_print(log_sock, printbuf);

	sprintf(printbuf, "[+] Kernel Text Base: 0x%lx\n", (unsigned long)KERNEL_ADDRESS_TEXT_BASE);
	sock_print(log_sock, printbuf);

	sprintf(printbuf, "[+] Kernel Data Base: 0x%lx\n", (unsigned long)kdata_base);
	sock_print(log_sock, printbuf);

	sprintf(printbuf, "[+] FW Version: 0x%x\n", kernel_get_fw_version());
	sock_print(log_sock, printbuf);

	sprintf(printbuf, "[+] Searching for kernel_pmap_store...\n");
	sock_print(log_sock, printbuf);

	pmap_offset = guess_kernel_pmap_store_offset(kdata_base);
	if (pmap_offset < 0) {
		sprintf(printbuf, "[-] Failed to find kernel_pmap_store, code = %zd\n",
		        -pmap_offset);
		sock_print(log_sock, printbuf);
		exit_code = ERR_PMAP_OFFSET_GUESS;
		goto out;
	}

	kernel_copyout(kdata_base + pmap_offset, &kernel_pmap_store,
	               sizeof(kernel_pmap_store));
	dmap_base = kernel_pmap_store.pm_pml4 - kernel_pmap_store.pm_cr3;

	sprintf(printbuf, "[+] kernel_pmap_store offset: 0x%zx\n", pmap_offset);
	sock_print(log_sock, printbuf);

	sprintf(printbuf, "[+] pm_pml4: 0x%lx, pm_cr3: 0x%lx\n",
	        (unsigned long)kernel_pmap_store.pm_pml4,
	        (unsigned long)kernel_pmap_store.pm_cr3);
	sock_print(log_sock, printbuf);

	sprintf(printbuf, "[+] dmap_base: 0x%zx\n", dmap_base);
	sock_print(log_sock, printbuf);

	sprintf(printbuf, "[+] Dump server listening on port %d\n", DUMP_SERVER_PORT);
	sock_print(log_sock, printbuf);

	dump_buf = malloc(DUMP_BUF_SIZE);
	if (dump_buf == NULL) {
		exit_code = ERR_DUMPER_BUF_MALLOC;
		goto out;
	}

	while (running > 0) {
		client = accept(dumper_sock, NULL, NULL);

		if (client > 0) {
			cmd_sz = read(client, cmd_buf, CMD_BUF_SIZE - 1);
			if (cmd_sz < 0) {
				close(client);
				continue;
			}
			cmd_buf[cmd_sz] = '\0';
			sprintf(printbuf, "[+] Command: %s\n", cmd_buf);
			sock_print(log_sock, printbuf);

			size_t dump_address = 0;
			size_t dump_size = 0;
			size_t vaddr_to_paddr_mode = 0;

			if (CMD_IS(CMD_STOP)) {
				running = 0;
				sprintf(printbuf, "[+] Stopping\n");
				sock_print(log_sock, printbuf);
				close(client);
				break;
			} else if (CMD_IS(CMD_DUMP_ABS)) {
				ret = sscanf(cmd_buf + sizeof(CMD_DUMP_ABS), "0x%zx 0x%zx",
				             &dump_address, &dump_size);
			} else if (CMD_IS(CMD_DUMP_BASE)) {
				ret = sscanf(cmd_buf + sizeof(CMD_DUMP_BASE), "0x%zx 0x%zx",
				             &dump_address, &dump_size);
				dump_address += kdata_base;
			} else if (CMD_IS(CMD_DUMP_PADDR)) {
				ret = sscanf(cmd_buf + sizeof(CMD_DUMP_PADDR), "0x%zx 0x%zx",
				             &dump_address, &dump_size);
				dump_address += dmap_base;
			} else if (CMD_IS(CMD_DUMP_VADDR)) {
				ret = sscanf(cmd_buf + sizeof(CMD_DUMP_VADDR), "0x%zx 0x%zx",
				             &dump_address, &dump_size);
				vaddr_to_paddr_mode = 1;
			} else if (CMD_IS(CMD_DUMP_RANGES)) {
				mem_ranges.len = 0;
				ret = collect_ranges(dmap_base, kernel_pmap_store.pm_cr3, 0, 0,
				                     &mem_ranges);
				sprintf(printbuf, "%d\n", ret < 0 ? (int)ret : (int)mem_ranges.len);
				sock_print(client, printbuf);
				if (ret == 0) {
					print_ranges(&mem_ranges, client);
				}
				close(client);
				continue;
			} else {
				close(client);
				continue;
			}

			if (ret < 2) {
				close(client);
				continue;
			}

			sprintf(printbuf, "[+] Dumping 0x%zx bytes from 0x%zx\n", dump_size,
			        dump_address);
			sock_print(log_sock, printbuf);

			size_t kpos = vaddr_to_paddr_mode ? 0 : dump_address;
			size_t page_end = 0;
			size_t dumped = 0;

			while (dumped < dump_size) {
				if (vaddr_to_paddr_mode && kpos == page_end) {
					size_t vaddr = dump_address + dumped;
					ssize_t paddr = vaddr_to_paddr(vaddr, dmap_base,
					                               kernel_pmap_store.pm_cr3,
					                               &page_end, log_sock);
					if (paddr < 0) {
						sprintf(printbuf, "[-] vaddr_to_paddr failed, code = %zd\n",
						        -paddr);
						sock_print(log_sock, printbuf);
						break;
					}
					sprintf(printbuf, "[+] vaddr 0x%zx -> paddr 0x%zx (page_end 0x%zx)\n",
					        vaddr, (size_t)paddr, page_end);
					sock_print(log_sock, printbuf);
					kpos = PADDR_TO_DMAP(paddr, dmap_base);
					page_end = PADDR_TO_DMAP(page_end, dmap_base);
				}

				size_t left = dump_size - dumped;
				if (vaddr_to_paddr_mode && ((page_end - kpos) < left)) {
					left = page_end - kpos;
				}
				size_t block_size = DUMP_BUF_SIZE;
				if (block_size > left) {
					block_size = left;
				}
				kernel_copyout(kpos, dump_buf, block_size);
				ret = write_buf(client, dump_buf, block_size);
				if (ret < 0) {
					sprintf(printbuf, "[-] Write to client failed\n");
					sock_print(log_sock, printbuf);
					break;
				}
				kpos += block_size;
				dumped += block_size;
			}
			close(client);
		}
	}

out:
	if (mem_ranges.ranges != NULL) {
		free(mem_ranges.ranges);
	}
	if (dump_buf != NULL) {
		free(dump_buf);
	}
	if (dumper_sock >= 0) {
		shutdown(dumper_sock, SHUT_RDWR);
		close(dumper_sock);
	}
	if (log_sock >= 0) {
		sprintf(printbuf, "[+] Exiting with code %d\n", exit_code);
		sock_print(log_sock, printbuf);
		shutdown(log_sock, SHUT_RDWR);
		close(log_sock);
	}
	return exit_code;
}
