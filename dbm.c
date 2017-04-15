/*
  This file is part of MAMBO, a low-overhead dynamic binary modification tool:
      https://github.com/beehive-lab/mambo

  Copyright 2013-2017 Cosmin Gorgovan <cosmin at linux-geek dot org>

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*/

#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <assert.h>
#include <string.h>
#include <limits.h>
#include <asm/unistd.h>
#include <pthread.h>

#include <sys/mman.h>
#include <unistd.h>

#include <libelf.h>

#include "dbm.h"
#include "common.h"
#include "scanner_common.h"

#include "elf_loader/elf_loader.h"

#ifdef __arm__
#include "pie/pie-thumb-decoder.h"
#include "pie/pie-thumb-encoder.h"
#include "pie/pie-arm-encoder.h"
#endif

#ifdef DEBUG
  #define debug(...) fprintf(stderr, __VA_ARGS__)
  #ifndef VERBOSE
    #define VERBOSE
  #endif
#else
  #define debug(...)
#endif

#ifdef VERBOSE
  #define info(...) fprintf(stderr, __VA_ARGS__)
#else
  #define info(...)
#endif

#define dispatcher_thread_data_offset ((uintptr_t)&disp_thread_data - (uintptr_t)&start_of_dispatcher_s)
#define th_is_pending_ptr_offset      ((uintptr_t)&th_is_pending_ptr - (uintptr_t)&start_of_dispatcher_s)
#define dispatcher_wrapper_offset     ((uintptr_t)dispatcher_trampoline - (uintptr_t)&start_of_dispatcher_s)
#define syscall_wrapper_offset        ((uintptr_t)syscall_wrapper - (uintptr_t)&start_of_dispatcher_s)
#define trace_head_incr_offset        ((uintptr_t)trace_head_incr - (uintptr_t)&start_of_dispatcher_s)

dbm_global global_data;
__thread dbm_thread *current_thread;

void flush_code_cache(dbm_thread *thread_data) {
  thread_data->was_flushed = true;
  // 0 is a reserved value telling the dispatcher not to attempt linking
  thread_data->free_block = 1;
  hash_init(&thread_data->entry_address, CODE_CACHE_HASH_SIZE + CODE_CACHE_HASH_OVERP);
  thread_data->bb_cache_next = &thread_data->code_cache->bbs[trampolines_size_bytes];
#ifdef DBM_TRACES
  thread_data->trace_cache_next = thread_data->code_cache->traces;
  thread_data->trace_id = BB_META_SIZE;
  thread_data->active_trace.id = BB_META_SIZE;
  thread_data->active_trace.active = false;

  hash_init(&thread_data->trace_entry_address, CODE_CACHE_HASH_SIZE + CODE_CACHE_HASH_OVERP);
#endif

  linked_list_init(thread_data->cc_links, MAX_CC_LINKS);
}

void mambo_deliver_callbacks(unsigned cb_id, dbm_thread *thread_data, inst_set inst_type,
                             cc_type fragment_type, int fragment_id, int inst, mambo_cond cond,
                             void *read_address, void *write_p, unsigned long *regs) {
#ifdef PLUGINS_NEW
  mambo_context ctx;

  assert(cb_id < CALLBACK_MAX_IDX);

  if (global_data.free_plugin > 0) {
    set_mambo_context(&ctx, thread_data, inst_type, fragment_type,
                      fragment_id, inst, cond, read_address, write_p, regs);
    for (int i = 0; i < global_data.free_plugin; i++) {
      if (global_data.plugins[i].cbs[cb_id] != NULL) {
        ctx.plugin_id = i;
        global_data.plugins[i].cbs[cb_id](&ctx);
      } // if
    } // for
  }
#endif
}

uintptr_t cc_lookup(dbm_thread *thread_data, uintptr_t target) {
  uintptr_t addr = hash_lookup(&thread_data->entry_address, target);
  return adjust_cc_entry(addr);
}

uintptr_t lookup_or_scan(dbm_thread *thread_data, uintptr_t target, bool *cached) {
  uintptr_t block_address;
  bool from_cache = true;
  uintptr_t basic_block;
  
  debug("Thread_data: %p\n", thread_data);
  
  block_address = cc_lookup(thread_data, target);

  if (block_address == UINT_MAX) {
    from_cache = false;
    block_address = scan(thread_data, (uint16_t *)target, -1);
  } else {
    if (is_bb(thread_data, block_address)) {
      basic_block = addr_to_bb_id(thread_data, block_address);
      assert(basic_block != -1);
      if (thread_data->code_cache_meta[basic_block].exit_branch_type == stub) {
        block_address = scan(thread_data, (uint16_t *)target, basic_block);
      }
    }
  }

  if (cached != NULL) {
    *cached = from_cache;
  }

  return block_address;
}

bool bb_cache_flush_if_full(dbm_thread *thread_data) {
  bool flushed = false;
  if (((uintptr_t)thread_data->code_cache->traces -
      (uintptr_t)thread_data->bb_cache_next) < MIN_FSPACE) {
    debug("BB cache full, flushing the CC\n");
    flush_code_cache(thread_data);
    flushed = true;
  } else if(thread_data->free_block >= (BB_META_SIZE - 1)) {
    debug("BB metadata full, flushing the CC\n");
    flush_code_cache(thread_data);
    flushed = true;
  }
  return flushed;
}

int allocate_bb(dbm_thread *thread_data) {
  unsigned int basic_block;
  basic_block = thread_data->free_block++;
  assert(basic_block < BB_META_SIZE);
  return basic_block;
}

#define BB_ALIGN 4 // must be power of 2
#ifdef __arm__
  // FIXME: sometimes we don't increment the write pointer after the last generated instruction
  #define BB_INCR 4
#else
  #define BB_INCR 0
#endif
uintptr_t allocate_cache_bb(dbm_thread *thread_data) {
  uintptr_t block_address = (uintptr_t)thread_data->bb_cache_next;
  block_address += BB_INCR;
  if (block_address & (BB_ALIGN-1)) {
    block_address &= ~(BB_ALIGN-1);
    block_address += BB_ALIGN;
  }
  thread_data->bb_cache_next = (void *)block_address;
  return block_address;
}

/* Stub BBs only contain a call to the dispatcher
   Stub BBs are used when a basic block can be optimised by directly linking
   to a target, but it's not clear if the target will ever be reached, e.g.:
   fallthrough path for conditional branches, RAS prediction */
uintptr_t stub_bb(dbm_thread *thread_data, uintptr_t target) {
  unsigned int basic_block;
  uintptr_t block_address;
  void *write_p;
  uintptr_t thumb = target & THUMB;

  bb_cache_flush_if_full(thread_data);
  basic_block = allocate_bb(thread_data);
  block_address = allocate_cache_bb(thread_data);
  
  debug("Stub BB: 0x%x\n", block_address + thumb);
  
  thread_data->code_cache_meta[basic_block].exit_branch_type = stub;
  thread_data->code_cache_meta[basic_block].tpc = block_address;
  thread_data->code_cache_meta[basic_block].linked_from = NULL;
  if (!hash_add(&thread_data->entry_address, target, block_address + thumb)) {
    fprintf(stderr, "Failed to add hash table entry for newly created stub basic block\n");
    while(1);
  }

  write_p = (void *)block_address;
#ifdef __arm__
  if (thumb) {
    thumb_encode_stub_bb(thread_data, (uint16_t **)&write_p, basic_block, target);
  } else {
    arm_encode_stub_bb(thread_data, (uint32_t **)&write_p, basic_block, target);
  }
#endif
#ifdef __aarch64__
  assert(0); // TODO
#endif
  __clear_cache(thread_data->bb_cache_next, write_p);
  thread_data->bb_cache_next = write_p;
  
  return adjust_cc_entry(block_address + thumb);
}

uintptr_t lookup_or_stub(dbm_thread *thread_data, uintptr_t target) {
  uintptr_t block_address;
  
  debug("Stub(0x%x)\n", target);
  debug("Thread_data: %p\n", thread_data);
  
  block_address = cc_lookup(thread_data, target);
  if (block_address == UINT_MAX) {
    block_address = stub_bb(thread_data, target);
  }

  return block_address;
}

#ifdef PLUGINS_NEW
void set_mambo_context(mambo_context *ctx, dbm_thread *thread_data, inst_set inst_type,
                       cc_type fragment_type, int fragment_id, int inst, mambo_cond cond,
                       void *read_address, void *write_p, unsigned long *regs) {
  ctx->thread_data = thread_data;
  ctx->inst_type = inst_type;
  ctx->fragment_type = fragment_type;
  ctx->fragment_id = fragment_id;
  ctx->inst = inst;
  ctx->cond = cond;
  ctx->read_address = read_address;
  ctx->write_p = write_p;
  ctx->regs = regs;
  ctx->replace = false;
  ctx->pushed_regs = 0;
  ctx->available_regs = 0;
  ctx->plugin_pushed_reg_count = 0;
}
#endif

#ifdef __arm__
int scanner_queue_add(scanner_queue_t *queue, void *link_to, uintptr_t spc, mambo_cond cond,
                      bool is_thumb, bool is_raw_addr, bool stub_only) {
#else
int scanner_queue_add(scanner_queue_t *queue, void *link_to, uintptr_t spc, bool is_raw_addr,
                      bool stub_only) {
#endif
  if (queue->len >= MAX_SCAN_QUEUE_LEN) {
    return -1;
  }

  int index = queue->len++;
  queue->entries[index].spc = spc;
  queue->entries[index].link_to = link_to;
  queue->entries[index].info = stub_only ? QUEUE_STUB_ONLY : 0;
  queue->entries[index].info |= is_raw_addr ? QUEUE_IS_RAW_ADDR : 0;
#ifdef __arm__
  queue->entries[index].info |= cond;
  queue->entries[index].info |= is_thumb ? QUEUE_IS_THUMB : 0;
#endif

  return 0;
}

void scanner_queue_process_entry(dbm_thread *thread_data, scanner_queue_entry *entry) {
  uintptr_t tpc;

  if (entry->info & QUEUE_STUB_ONLY) {
    tpc = lookup_or_stub(thread_data, entry->spc);
  } else {
    tpc = lookup_or_scan(thread_data, entry->spc, NULL);
  }
  if (entry->info & QUEUE_IS_RAW_ADDR) {
    uintptr_t *target = (uintptr_t *)entry->link_to;
    *target = tpc;
    record_cc_link(thread_data, ((uintptr_t)target) | FULLADDR, tpc);
  } else {
#ifdef __arm__
    if (entry->info & QUEUE_IS_THUMB) {
      thumb_cc_branch(thread_data, entry->link_to, tpc);
    } else {
      arm_cc_branch(thread_data, entry->link_to, tpc, entry->info & QUEUE_COND_MASK);
    }
#elif __aarch64__
    a64_cc_branch(thread_data, (uint32_t *)entry->link_to, tpc);
#endif
  }
}

void scanner_queue_process(dbm_thread *thread_data, scanner_queue_t *queue) {
  // First process the scan requests
  for (int i = queue->len - 1; i >= 0; i--) {
    if ((queue->entries[i].info & QUEUE_STUB_ONLY) == 0) {
      scanner_queue_process_entry(thread_data, &queue->entries[i]);
    }
  }

  // Then process the stub requests
  for (int i = queue->len - 1; i >= 0; i--) {
    if (queue->entries[i].info & QUEUE_STUB_ONLY) {
      scanner_queue_process_entry(thread_data, &queue->entries[i]);
    }
  }
}

void rewrite_cc_branches(dbm_thread *thread_data, int bb_id, uintptr_t new_target) {
  uintptr_t orig_branch;
  ll_entry *cc_link = thread_data->code_cache_meta[bb_id].linked_from;

  while(cc_link != NULL) {
    orig_branch = cc_link->data;
#ifdef __arm__
    orig_branch &= 0xFFFFFFFE;
    if (cc_link->data & THUMB) {
      thumb_adjust_b_bl_target(thread_data, (uint16_t *)orig_branch, new_target);
    } else if ((cc_link->data & 3) == FULLADDR) {
      *(uint32_t *)(orig_branch & (~FULLADDR)) = new_target;
    } else {
      arm_adjust_b_bl_target((uintptr_t *)orig_branch, new_target);
    }
#elif __aarch64__
    a64_b_helper((uint32_t *)orig_branch, new_target);
#endif
    cc_link = cc_link->next;
    __clear_cache((void *)orig_branch, (void *)orig_branch + 4);
  }
}

uintptr_t scan(dbm_thread *thread_data, uint16_t *address, int stub_id) {
  uintptr_t thumb = (uintptr_t)address & THUMB;
  uintptr_t block_address;
  size_t block_size;
  bool stub = false;
  scanner_queue_t scan_queue;
  scan_queue.len = 0;
  int basic_block;

  debug("scan(%p)\n", address);

  bb_cache_flush_if_full(thread_data);
  basic_block = allocate_bb(thread_data);
  block_address = allocate_cache_bb(thread_data);
  if (stub_id >= 0) {
    rewrite_cc_branches(thread_data, stub_id, adjust_cc_entry(block_address | thumb));
    thread_data->code_cache_meta[basic_block].linked_from =
                 thread_data->code_cache_meta[stub_id].linked_from;
  } else {
    thread_data->code_cache_meta[basic_block].linked_from = NULL;
  }

  thread_data->code_cache_meta[basic_block].source_addr = address;
  thread_data->code_cache_meta[basic_block].tpc = block_address;
  thread_data->code_cache_meta[basic_block].exit_branch_type = unknown;
  thread_data->code_cache_meta[basic_block].branch_cache_status = 0;
#ifdef DBM_TRACES
  thread_data->exec_count[basic_block] = 0;
#endif

  //fprintf(stderr, "scan(%p): 0x%x (bb %d)\n", address, block_address, basic_block);

  // Add entry into the code cache hash table
  // It must be added before scanner_queue_process() is called, otherwise a queued scan
  // from scan_x could result in duplicate BBS or an infinite recursive call
  if (!hash_add(&thread_data->entry_address, (uintptr_t)address, block_address | thumb)) {
    fprintf(stderr, "Failed to add hash table entry for newly created basic block\n");
    while(1);
  }

  mambo_deliver_callbacks(PRE_FRAGMENT_C, thread_data, thumb ? THUMB_INST : ARM_INST, mambo_bb,
                          basic_block, -1, -1, address, (void *)block_address, NULL);

  // Build a basic block
  // Scan functions return size of the generated basic block, in bytes
#ifdef __arm__
  if (thumb) {
    debug("scan address: %p\n", address);
    block_size = scan_thumb(thread_data, (uint16_t *)((uint32_t)address & 0xFFFFFFFE),
                            basic_block, mambo_bb, (uint16_t *)block_address, &scan_queue);
  } else {
    block_size = scan_arm(thread_data, (uint32_t *)address, basic_block,
                          mambo_bb, (uint32_t *)block_address, &scan_queue);
  }
#endif
#ifdef __aarch64__
  block_size = scan_a64(thread_data, (uint32_t *)address, basic_block, mambo_bb,
                        (uint32_t *)block_address, &scan_queue);
#endif

  mambo_deliver_callbacks(POST_FRAGMENT_C, thread_data, thumb ? THUMB_INST : ARM_INST, mambo_bb,
                          basic_block, -1, -1, address, (void *)block_address, NULL);

  thread_data->bb_cache_next += block_size;

  scanner_queue_process(thread_data, &scan_queue);

  // Flush modified instructions from caches
  // End address is exclusive
  if (thread_data->was_flushed) {
    /* The code cache has been flushed. Play it safe, because we don't know how
       much space has been used in each of the two areas. */
    __clear_cache((char *)block_address, &thread_data->code_cache->traces);
    __clear_cache(&thread_data->code_cache->bbs[trampolines_size_bytes],
                  thread_data->bb_cache_next);
  } else {
    __clear_cache((char *)block_address, (char *)(block_address + block_size + 1));
  }

  return adjust_cc_entry(block_address | thumb);
}

void dbm_exit(dbm_thread *thread_data, uint32_t code) {
  int bb_count = thread_data->entry_address.count;
  int collision_rate = thread_data->entry_address.collisions * 1000 / bb_count;

  fprintf(stderr, "We're done; exiting with status: %d\n", code);

  mambo_deliver_callbacks(POST_THREAD_C, thread_data, -1, -1, -1, -1, -1, NULL, NULL, NULL);
  mambo_deliver_callbacks(EXIT_C, thread_data, -1, -1, -1, -1, -1, NULL, NULL, NULL);

  info("MAMBO exit\n");

  exit(code);
}

bool allocate_thread_data(dbm_thread **thread_data) {
  dbm_thread *data = mmap(NULL, sizeof(dbm_thread), PROT_READ | PROT_WRITE, METADATA_MMAP_OPTS, -1, 0);
  if (data != MAP_FAILED) {
    *thread_data = data;
    return true;
  }
  return false;
}

void init_thread(dbm_thread *thread_data) {
  dbm_thread **dispatcher_thread_data;

  // Initialize code cache
  thread_data->code_cache = mmap(NULL, sizeof(dbm_code_cache), PROT_EXEC | PROT_READ | PROT_WRITE, CC_MMAP_OPTS, -1, 0);
  if (thread_data->code_cache == MAP_FAILED) {
    fprintf(stderr, "Allocating code cache space failed\n");
    while(1);
  }
  info("Code cache: %p\n", thread_data->code_cache);

  thread_data->cc_links = mmap(NULL, sizeof(ll) + sizeof(ll_entry) * MAX_CC_LINKS, PROT_READ | PROT_WRITE, METADATA_MMAP_OPTS, -1, 0);
  assert(thread_data->cc_links != MAP_FAILED);

  // Initialize the hash table and basic block allocator, mark all BBs as unknown type
  flush_code_cache(thread_data);

  // Copy the trampolines to the code cache
  memcpy(thread_data->code_cache->bbs, &start_of_dispatcher_s, trampolines_size_bytes);

  dispatcher_thread_data = (dbm_thread **)((uintptr_t)thread_data->code_cache->bbs
                                           + dispatcher_thread_data_offset);
  *dispatcher_thread_data = thread_data;

  uint32_t **dispatcher_is_pending = (uint32_t **)((uintptr_t)thread_data->code_cache->bbs
                                           + th_is_pending_ptr_offset);
  *dispatcher_is_pending = &thread_data->is_signal_pending;

  debug("*thread_data in dispatcher at: %p\n", dispatcher_thread_data);

#ifdef DBM_TRACES
  thread_data->trace_head_incr_addr = (uintptr_t)&thread_data->code_cache[0] + trace_head_incr_offset;

  #ifdef __arm__
  uint16_t *write_p = (uint16_t *)(thread_data->trace_head_incr_addr + 4 - 1);
  copy_to_reg_32bit(&write_p, r1, (uint32_t)thread_data->exec_count);
  #endif
  #ifdef __aarch64__
  uint32_t *write_p = (uint32_t *)(thread_data->trace_head_incr_addr + 4);
  a64_copy_to_reg_64bits(&write_p, x2, (uintptr_t)thread_data->exec_count);
  #endif

  info("Traces start at: %p\n", &thread_data->code_cache->traces);
#endif // DBM_TRACES

  __clear_cache(thread_data->code_cache->bbs, thread_data->bb_cache_next);
 
  thread_data->dispatcher_addr = (uintptr_t)&thread_data->code_cache[0] + dispatcher_wrapper_offset;
  thread_data->syscall_wrapper_addr = (uintptr_t)&thread_data->code_cache[0] + syscall_wrapper_offset;

  thread_data->is_vfork_child = false;
                        
  debug("Syscall wrapper addr: 0x%x\n", thread_data->syscall_wrapper_addr);

  mambo_deliver_callbacks(PRE_THREAD_C, thread_data, -1, -1, -1, -1, -1, NULL, NULL, NULL);
}

bool is_bb(dbm_thread *thread_data, uintptr_t addr) {
  uintptr_t min = (uintptr_t)thread_data->code_cache->bbs;
  uintptr_t max = (uintptr_t)thread_data->code_cache->traces;

  return addr >= min && addr < max;
}

int addr_to_cc_id(dbm_thread *thread_data, void *cc_start, void *cc_end,
                  int first_fr, int last_fr, uintptr_t addr) {
  uintptr_t start_addr = (uintptr_t )cc_start;
  uintptr_t end_addr = (uintptr_t)cc_end;

  if (addr < start_addr || addr >= end_addr) {
    return -1;
  }

  int pivot;

  if (addr >= thread_data->code_cache_meta[last_fr].tpc) {
    return last_fr;
  }

  while (first_fr <= last_fr) {
    pivot = (first_fr + last_fr) / 2;
    if (addr < thread_data->code_cache_meta[pivot].tpc) {
      last_fr = pivot - 1;
    } else if (addr >= thread_data->code_cache_meta[pivot+1].tpc) {
      first_fr = pivot + 1;
    } else {
      return pivot;
    }
  }

  return -1;
}

int addr_to_bb_id(dbm_thread *thread_data, uintptr_t addr) {
  return addr_to_cc_id(thread_data, &thread_data->code_cache->bbs[trampolines_size_bytes],
                       thread_data->code_cache->traces, 0, thread_data->free_block-1, addr);
}

int addr_to_fragment_id(dbm_thread *thread_data, uintptr_t addr) {
  uintptr_t start = (uintptr_t )thread_data->code_cache->bbs;
  assert(addr >= start && addr < (start + TOTAL_CC_SIZE));

  int id = addr_to_bb_id(thread_data, addr);
  if (id >= 0) {
    return id;
  }

#ifdef DBM_TRACES
  return addr_to_cc_id(thread_data, thread_data->code_cache->traces,
                       &thread_data->code_cache->traces[0] + TRACE_CACHE_SIZE,
                       BB_META_SIZE, thread_data->active_trace.id -1, addr);
#endif

  return -1;
}

// TODO: handle links to traces
void record_cc_link(dbm_thread *thread_data, uintptr_t linked_from, uintptr_t linked_to_addr) {
  int linked_to = addr_to_bb_id(thread_data, linked_to_addr);

  debug("Linked 0x%x (%d) from 0x%x\n", linked_to_addr, linked_to, linked_from);

  if (linked_to < 0) return;

  ll_entry *entry = linked_list_alloc(thread_data->cc_links);
  assert(entry != NULL);

  entry->data = linked_from;
  entry->next = thread_data->code_cache_meta[linked_to].linked_from;
  thread_data->code_cache_meta[linked_to].linked_from = entry;
}

void main(int argc, char **argv, char **envp) {
  Elf *elf = NULL;
  int has_interp = 0;
  int arg_diff;
  uintptr_t phdr;
  size_t phnum;
  
  if (argc < 2) {
    printf("Syntax: dbm elf_file arguments\n");
    exit(EXIT_FAILURE);
  }

  global_data.argc = argc;
  global_data.argv = argv;

  int ret = interval_map_init(&global_data.exec_allocs, 512);
  assert(ret == 0);

  ret = pthread_mutex_init(&global_data.signal_handlers_mutex, NULL);
  assert(ret == 0);

  install_system_sig_handlers();

  global_data.brk = 0;
  load_elf(argv[1], &elf, &has_interp, &phdr, &phnum);

  // Set up brk emulation
  ret = pthread_mutex_init(&global_data.brk_mutex, NULL);
  assert(ret == 0);
  global_data.initial_brk = global_data.brk;
  void *map = mmap((void *)global_data.brk, PAGE_SIZE, PROT_READ | PROT_WRITE,
                     MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED, -1, 0);
  assert(map != MAP_FAILED);
  global_data.brk += PAGE_SIZE;

  ELF_EHDR *ehdr = ELF_GETEHDR(elf);
  uintptr_t entry_address = ehdr->e_entry;
  if (ehdr->e_type == ET_DYN) entry_address += DYN_OBJ_OFFSET;
  uintptr_t block_address;
  debug("entry address: 0x%x\n", entry_address);
  
  dbm_thread *thread_data;
  if (!allocate_thread_data(&thread_data)) {
    fprintf(stderr, "Failed to allocate initial thread data\n");
    while(1);
  }
  current_thread = thread_data;
  init_thread(thread_data);
  thread_data->tid = syscall(__NR_gettid);

  block_address = scan(thread_data, (uint16_t *)entry_address, -1);
  debug("Address of first basic block is: 0x%x\n", block_address);
  
  arg_diff = has_interp ? 1 : 2;
  
  elf_run(block_address, entry_address, (has_interp ? "" : argv[1]), phdr, phnum, argc-arg_diff, &argv[arg_diff], envp);
}

