#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#include "memory.h"
#include "fail.h"
#include "engine.h"

#if GC_VERSION == GC_MARK_N_SWEEP

static void* memory_start = NULL;
static void* memory_end = NULL;

static uvalue_t* bitmap_start = NULL;

static value_t* heap_start = NULL;
static value_t* heap_end = NULL;
static value_t heap_start_v = 0;
static value_t heap_end_v = 0;
static value_t* heap_first_block = NULL;
static value_t allocateCounter = 0;
static value_t markCounter = 0;
static value_t freeCounter = 0;

#define FREE_LISTS_COUNT 32
static value_t* free_list_heads[FREE_LISTS_COUNT];

#define MIN_BLOCK_SIZE 1
#define HEADER_SIZE 1

// Header management

static value_t header_pack(tag_t tag, value_t size) {
  return (size << 8) | (value_t)tag;
}

static tag_t header_unpack_tag(value_t header) {
  return (tag_t)(header & 0xFF);
}

static value_t header_unpack_size(value_t header) {
  return header >> 8;
}

// Bitmap management

static int bitmap_is_bit_set(value_t* ptr) {
  assert(heap_start <= ptr && ptr < heap_end);
  long index = ptr - heap_start;
  long word_index = index / (long)VALUE_BITS;
  long bit_index = index % (long)VALUE_BITS;
  return (bitmap_start[word_index] & ((uvalue_t)1 << bit_index)) != 0;
}

static void bitmap_set_bit(value_t* ptr) {
  assert(heap_start <= ptr && ptr < heap_end);
  long index = ptr - heap_start;
  long word_index = index / (long)VALUE_BITS;
  long bit_index = index % (long)VALUE_BITS;
  bitmap_start[word_index] |= (uvalue_t)1 << bit_index;
}

static void bitmap_clear_bit(value_t* ptr) {
  assert(heap_start <= ptr && ptr < heap_end);
  long index = ptr - heap_start;
  long word_index = index / (long)VALUE_BITS;
  long bit_index = index % (long)VALUE_BITS;
  bitmap_start[word_index] &= ~((uvalue_t)1 << bit_index);
}

// Virtual <-> physical address translation

static void* addr_v_to_p(value_t v_addr) {
  return (char*)memory_start + v_addr;
}

static value_t addr_p_to_v(void* p_addr) {
  return (value_t)((char*)p_addr - (char*)memory_start);
}

// Free lists management

static value_t real_size(value_t size) {
  assert(0 <= size);
  return size < MIN_BLOCK_SIZE ? MIN_BLOCK_SIZE : size;
}

static unsigned int free_list_index(value_t size) {
  assert(0 <= size);
  return size >= FREE_LISTS_COUNT ? FREE_LISTS_COUNT - 1 : (unsigned int)size;
}

char* memory_get_identity() {
  return "mark & sweep garbage collector";
}

void memory_setup(size_t total_byte_size) {
  memory_start = malloc(total_byte_size);
  if (memory_start == NULL)
    fail("cannot allocate %zd bytes of memory", total_byte_size);
  memory_end = (char*)memory_start + total_byte_size;
}

void memory_cleanup() {
  assert(memory_start != NULL);
  free(memory_start);

  memory_start = memory_end = NULL;
  bitmap_start = NULL;
  heap_start = heap_end = NULL;
  heap_start_v = heap_end_v = 0;
  for (int l = 0; l < FREE_LISTS_COUNT; ++l)
    free_list_heads[l] = NULL;
}

void* memory_get_start() {
  return memory_start;
}

void* memory_get_end() {
  return memory_end;
}

void memory_set_heap_start(void* ptr) {
  assert(memory_start <= ptr && ptr < memory_end);

  const size_t bh_size =
    (size_t)((char*)memory_end - (char*)ptr) / sizeof(value_t);

  const size_t bitmap_size = (bh_size - 1) / (VALUE_BITS + 1) + 1;
  const size_t heap_size = bh_size - bitmap_size;

  bitmap_start = ptr;
  //set memory with constant byte
  memset(bitmap_start, 0, bitmap_size * sizeof(value_t));

  heap_start = (value_t*)bitmap_start + bitmap_size;
  heap_end = heap_start + heap_size;
  assert(heap_end == memory_end);

  heap_start_v = addr_p_to_v(heap_start);
  heap_end_v = addr_p_to_v(heap_end);

  heap_first_block = heap_start + HEADER_SIZE;
  const value_t initial_block_size = (value_t)(heap_end - heap_first_block);
  heap_first_block[-1] = header_pack(tag_None, initial_block_size);
  heap_first_block[0] = 0;

  for (int l = 0; l < FREE_LISTS_COUNT - 1; ++l)
    free_list_heads[l] = memory_start;
  
  memory_set_next_pointer(heap_first_block, NULL);
  free_list_heads[FREE_LISTS_COUNT - 1] = heap_first_block;
}

static value_t* allocate(tag_t tag, value_t given_size) {
  fprintf(stderr, "\n<Allocate>\n");

  next_pointer * head;          //to traverse the free list
  next_pointer * prev;          //the prev block in the free list
  value_t* alloc_block = NULL;  //allocated block
  value_t block_size;           //contains size of the current block in free list

  value_t size = real_size(given_size);       //update size of too small (min = size of next_pointer)

  if(free_list_heads[FREE_LISTS_COUNT - 1] == NULL) {
    return NULL;
  }

  //initialize runners
  head = (next_pointer *) free_list_heads[FREE_LISTS_COUNT - 1];
  prev = NULL;

  /*----DEGBUG-----*/
  fprintf(stderr, "head: %d\n", head);
  if(freeCounter > 0) {
    //after sweep
    int y = 0;
  }
  /*---------------*/

  //loop through freelist
  while((value_t*)head != NULL && (value_t)head != 0) {

    /*----DEGBUG-----*/
    fprintf(stderr, "head -> next: %d\n", head -> next);

    //when next node is not in heap
    if(head -> next < heap_start && (value_t)(head->next) != 0) {
      int x = 0;
    }

    // fprintf(stderr, "head: %d\n", head);
    if((value_t*) head < heap_start || (value_t*) head > heap_end) {
      fprintf(stderr, "head: %d\n", head);
      assert((value_t*) head >= heap_start && (value_t*) head < heap_end);
    }
    /*---------------*/

    block_size = memory_get_block_size((value_t*) head);
    
    //if size fits
    if(size <= block_size) {
      fprintf(stderr, "--- allocating ---\n");
      
      //if block cannot be split
      if(block_too_small_to_split(size, block_size)) {
        allocateCounter += block_size;
        alloc_block = (value_t*)head;

        //update next pointer
        if(prev == NULL) {
          if((value_t)(head -> next) == 0) {
            free_list_heads[FREE_LISTS_COUNT - 1] = NULL;
          } else {
            free_list_heads[FREE_LISTS_COUNT - 1] = head -> next;
            fprintf(stderr, "---removed rom freelist---\n");
          }
          
        } else {
          memory_set_next_pointer((value_t*)prev, head -> next);
          fprintf(stderr, "---removed rom freelist---\n");
        }

        //set all values to 0
        memset(alloc_block, 0, block_size * sizeof(value_t));

        //update tag
        memory_set_block_size_and_tag(alloc_block, tag, block_size);

        break;
      }

      // fprintf(stderr, "\n Split \n");
      allocateCounter += size + HEADER_SIZE;

      //if block can be split
      tag_t current_tag = memory_get_block_tag((value_t*)head);
      value_t new_head_size = block_size - (size + HEADER_SIZE);

      //update current block's size
      memory_set_block_size_and_tag((value_t*)head, current_tag, new_head_size);

      //create the alloc block
      alloc_block = ((value_t*) head) + new_head_size + HEADER_SIZE;
      memory_set_block_size_and_tag(alloc_block, tag, size);

      //set all values to 0
      memset(alloc_block, 0, size * sizeof(value_t));

      break;
    }

    //go to next free node
    prev = head;
    // fprintf(stderr, "head: %d\n", head);
    head = (next_pointer *)(head -> next);
    // fprintf(stderr, "head: %d\n", head);
  }

  if(alloc_block != NULL) {
    bitmap_set_bit(alloc_block);
  }

  return alloc_block;
}

static void mark(value_t* block) {
  // fprintf(stderr, "<Mark>\n");

  // reset bit in map if it was set before and check further references.
  int i = 0;
  value_t size = real_size(memory_get_block_size(block));
  for(i = 0; i < size; i++) {

    value_t stored_value = *(block + i);
    
    //check if value is in heap
    if(stored_value < heap_start_v || stored_value >= heap_end_v) {
      continue;
    }

    //if it is in the bitmap
    if(bitmap_is_bit_set(addr_v_to_p(stored_value))) {
      bitmap_clear_bit(addr_v_to_p(stored_value));
      markCounter++;
      mark(addr_v_to_p(stored_value));
    }
  }

  // fprintf(stderr, "</Mark>\n");
}

static void sweep() {
  fprintf(stderr, "\n\n<Sweep>\n");
  fprintf(stderr, "allocated: %d\t marked: %d\n", allocateCounter, markCounter);

  // TODO
  // find freeable block (bits not reset in bitmap)
  value_t* block = heap_first_block; //first block in the heap
  value_t* new_free_list = NULL; //the new free list
  value_t* current = new_free_list;  //current node in the free list

  int flag = 0; //keeps track of consecutive blocks for coalescing

  //set bits for all free blocks
  setFreeBits();

  for(; block < heap_end; block = block + real_size(memory_get_block_size(block)) + HEADER_SIZE) {
    assert(block >= heap_start && block < heap_end);

    value_t block_size = real_size(memory_get_block_size(block));
    // assert(block + block_size + HEADER_SIZE < heap_end && block + block_size + HEADER_SIZE  >= heap_start);
    // if(current != NULL) {
    //   fprintf(stderr, "current: %d\n", ((next_pointer*)current) -> next);
    // }

    // if(block_size == 0) {
    //   fprintf(stderr,"-- 0 size --\n");
    //   fprintf(stderr, "heap_end: %d\t block: %d\n", heap_end, block);
    //   // break;
    // }
   
    //check for sweepability
    if(bitmap_is_bit_set(block)) {
      // fprintf(stderr,"--- free ---\n");
      bitmap_clear_bit(block);

      freeCounter+= block_size;
      //first block
      if(new_free_list == NULL) {
        // fprintf(stderr,"---Only Once---\n");
        memory_set_next_pointer(block, NULL);
        new_free_list = block;
        current = block;
        assert(current >= heap_start && current < heap_end);
        continue;
      }

      //coalesce
      if(flag) {
        // fprintf(stderr,"--- coalesce ---\n");
        value_t current_size = memory_get_block_size(current);
        value_t current_tag = memory_get_block_tag(current);
        // fprintf(stderr, "prev size: %d\t new size: %d\n", current_size, current_size + block_size + HEADER_SIZE);
        memory_set_block_size_and_tag(current, current_tag, current_size + block_size + HEADER_SIZE);
        assert(current >= heap_start && current < heap_end);
        continue;
      } 
      // fprintf(stderr,"--- no coalesce ---\n");
      memory_set_next_pointer(current, block);
      // fprintf(stderr, "current change: %d\n", ((next_pointer*)current) -> next);
      assert(((next_pointer*)current) -> next >= heap_start && ((next_pointer*)current) -> next < heap_end);
      memory_set_next_pointer(block, NULL);
      current = block;
      assert(current >= heap_start && current < heap_end);

      //set up consecutive block
      flag = 1;

    } else {
      // fprintf(stderr,"--- not free ---\n");
      assert(block >= heap_start && block < heap_end);
      //set bit in bitmap
      bitmap_set_bit(block); 

      //not consecutive blocks
      flag = 0;
    }
  }

  next_pointer* p = (next_pointer*)new_free_list;
  while(p != NULL && (value_t)p != 0) {
    fprintf(stderr, "p: %d\n", p);
    p = (next_pointer*)(p -> next);
  }

  fprintf(stderr, "block: %d\t heap end: %d\n", block, heap_end);
  fprintf(stderr, "free: %d\n", freeCounter);
  fprintf(stderr, "</Sweep>\n\n");
  // freeCounter = 0;
  allocateCounter = 0;
  markCounter = 0;
  free_list_heads[FREE_LISTS_COUNT - 1] = new_free_list;
}

void setFreeBits() {
  next_pointer * head = (next_pointer *) free_list_heads[FREE_LISTS_COUNT - 1];
  while(head != NULL) {
    fprintf(stderr, "ahkajshda");
    assert((value_t*)head >= heap_start && (value_t*)head < heap_end);
    bitmap_set_bit((value_t *) head);
    markCounter++;
    head = (next_pointer *) head -> next;
  }
}

value_t* memory_allocate(tag_t tag, value_t size) {
  value_t* first_try = allocate(tag, size);
  if (first_try != NULL)
    return first_try;

  value_t* lb = engine_get_Lb();
  if (lb != memory_start) mark(lb);
  value_t* ib = engine_get_Ib();
  if (ib != memory_start) mark(ib);
  value_t* ob = engine_get_Ob();
  if (ob != memory_start) mark(ob);

  sweep();

  value_t* second_try = allocate(tag, size);
  if (second_try != NULL)
    return second_try;

  fail("\ncannot allocate %d words of memory, even after GC\n", size);
}

void memory_set_block_size_and_tag(value_t* block, tag_t tag, value_t size) {
  block[-1] = header_pack(tag, size);
}

void memory_set_next_pointer(value_t* block, value_t* ptr) {
  next_pointer* block_next = (next_pointer *) block;
  block_next -> next = ptr;
}

value_t memory_get_block_size(value_t* block) {
  return header_unpack_size(block[-1]);
}

tag_t memory_get_block_tag(value_t* block) {
  return header_unpack_tag(block[-1]);
}

int block_too_small_to_split(value_t size, value_t block_size) {
  //size of header + size of next_pointer
  return (block_size - size) < 2 * MIN_BLOCK_SIZE;
}

// void checkHeap() {
//   value_t* head = heap_first_block;
//   value_t size;
//   while(head < heap_end) {
//     size = memory_get_block_size(head);
//     head = head + real_size(size);
//   }

//   fprintf(stderr, "heap end: %d\t last block: %d\n", heap_end, head);
//   assert(head == heap_end);
// }

#endif
