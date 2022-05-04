#include "gc.h"
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef uint64_t SNAKEVAL;

void printHelp(FILE *out, SNAKEVAL val);

extern uint64_t NUM_TAG;
extern uint64_t BOOL_TAG;
extern uint64_t TUPLE_TAG;
extern uint64_t CLOSURE_TAG;
extern uint64_t STRUCT_TAG;
extern uint64_t PTR_TAG;
extern uint64_t BOOL_TRUE;
extern uint64_t BOOL_FALSE;
extern uint64_t NIL;

extern uint64_t NUM_TAG_MASK;
extern uint64_t BOOL_TAG_MASK;
extern uint64_t TUPLE_TAG_MASK;
extern uint64_t CLOSURE_TAG_MASK;
extern uint64_t STRUCT_TAG_MASK;
extern uint64_t PTR_TAG_MASK;

extern uint64_t *STACK_BOTTOM;
extern uint64_t *FROM_S;
extern uint64_t *FROM_E;
extern uint64_t *TO_S;
extern uint64_t *TO_E;

#define LOG 0 // change to enable logging

void naive_print_heap(uint64_t *heap, uint64_t *heap_end) {
  printf("In naive_print_heap from %p to %p\n", heap, heap_end);
  for (uint64_t i = 0; i < (uint64_t)(heap_end - heap); i += 1) {
    printf("  %ld/%p: %p (%ld)\n", i, (heap + i), (uint64_t *)(*(heap + i)),
           *(heap + i));
  }
}

/*
  Smarter algorithm to print the contents of the heap.  You should implement
  this function much like the naive approach above, but try to have it print out
  values as Garter values

  Arguments:
    from_start: the starting address (inclusive) of the from-space of the heap
    from_end: the ending address (exclusive) of the from-space of the heap
    to_start: the starting address (inclusive) of the to-space of the heap
    to_end: the ending address (exclusive) of the to-space of the heap
 */
void smarter_print_heap(uint64_t *from_start, uint64_t *from_end,
                        uint64_t *to_start, uint64_t *to_end) {
  printf("Smarter Print Heap:\n");
  printf("HEAP FROM (from %#018lx to %#018lx):\n", (uint64_t)from_start,
         (uint64_t)from_end);
  for (uint64_t i = 0; i < (uint64_t)(from_end - from_start); i += 1) {
    printf("  %ld/%p: %p -> ", i, (from_start + i),
           (uint64_t *)(*(from_start + i)));
    printHelp(stdout, *(from_start + i));
    printf("\n");
  }

  printf("HEAP TO (from %#018lx to %#018lx):\n", (uint64_t)to_start,
         (uint64_t)to_end);
  for (uint64_t i = 0; i < (uint64_t)(to_end - to_start); i += 1) {
    printf("  %ld/%p: %p -> ", i, (to_start + i),
           (uint64_t *)(*(to_start + i)));
    printHelp(stdout, *(to_start + i));
    printf("\n");
  }
}

/*
  Copies a closure from its position on the current heap to the new heap

  Arguments:
    garter_val_addr: the address of the tagged closure, contains the tagged
  closure heap_top: the location to begin copying
    heap_top: the location to begin copying
*/
uint64_t *copy_closure(uint64_t *garter_val_addr, uint64_t *heap_top) {
  SNAKEVAL garter_val = *garter_val_addr;
  uint64_t *heap_closure_addr = (uint64_t *)(garter_val - CLOSURE_TAG);
  if ((*heap_closure_addr & PTR_TAG_MASK) == PTR_TAG) {
    // If garter_val is a (tagged) pointer to a heap_thing that now contains a
    // forwarding pointer, replace the value at garter_val_addr with the
    // appropriately tagged version of that forwarding pointer
    uint64_t *fw_ptr = (uint64_t *)(*heap_closure_addr - PTR_TAG);
#if LOG
    printf("FWD PTR IN CLOSURE!!!!!: %018lx\n", (uint64_t)fw_ptr);
#endif
    uint64_t retagged_fw_ptr = (uint64_t)fw_ptr + CLOSURE_TAG;
    *garter_val_addr = retagged_fw_ptr;
    return heap_top;
  }

#if LOG
  printf("copying closure: ");
  printHelp(stdout, garter_val);
  printf("\n");
#endif

  // Copy the full contents of heap_thing to heap_top
  uint64_t num_free_vars = heap_closure_addr[2] / 2;
  uint64_t padding = (3 + num_free_vars) % 2;
  uint64_t total_closure_size = (3 + num_free_vars + padding);
  for (uint64_t i = 0; i < total_closure_size; i++) {
    heap_top[i] = heap_closure_addr[i];
  }

#if LOG
  printf("arity for closure: %ld\n", heap_closure_addr[0] / 2);
  printf("number of free vars for closure: %ld\n", num_free_vars);
#endif

  // Update the value at garter_val_addr with the value of heap_top.
  garter_val_addr = heap_top;

  // Replace the value at heap_thing_addr (i.e., the location referred to by
  // garter_val) with a forwarding pointer to heap_top.
  uint64_t ptr = ((uint64_t)heap_top) + PTR_TAG;
  *heap_closure_addr = ptr;

  // Increment heap_top as needed to record the allocation.
  heap_top += total_closure_size;

  // For each field within heap_thing at the new location, recursively call
  // copy_if_needed (Be careful about using the return value of those calls
  // correctly!)
  for (int i = 0; i < num_free_vars; i += 1) {
#if LOG
    printf("Index of free var copying: %d - snakeval value: ", i);
    printHelp(stdout, garter_val_addr[i + 3]);
    printf("\n");
#endif
    heap_top = copy_if_needed(&garter_val_addr[i + 3], heap_top);
  }

#if LOG
  printf("return heap_top in closure: %#018lx\n", (uint64_t)heap_top);
#endif
  // Return the current heap_top
  return heap_top;
}

/*
  Copies a struct from its position on the current heap to the new heap

  Arguments:
    garter_val_addr: the address of the tagged struct, contains the tagged
  struct heap_top: the location to begin copying
*/
uint64_t *copy_struct(uint64_t *garter_val_addr, uint64_t *heap_top) {
  SNAKEVAL garter_val = *garter_val_addr;
  uint64_t *heap_struct_addr = (uint64_t *)(garter_val - STRUCT_TAG);
  if ((*heap_struct_addr & PTR_TAG_MASK) == PTR_TAG) {
    // If garter_val is a (tagged) pointer to a heap_thing that now contains a
    // forwarding pointer, replace the value at garter_val_addr with the
    // appropriately tagged version of that forwarding pointer
    uint64_t *fw_ptr = (uint64_t *)(*heap_struct_addr - PTR_TAG);
#if LOG
    printf("FWD PTR IN STRUCT!!!!!: %018lx\n", (uint64_t)fw_ptr);
#endif
    uint64_t retagged_fw_ptr = (uint64_t)fw_ptr + STRUCT_TAG;
    *garter_val_addr = retagged_fw_ptr;
    return heap_top;
  }

#if LOG
  printf("copying struct: ");
  printHelp(stdout, garter_val);
  printf("\n");
#endif

  // Copy the full contents of heap_thing to heap_top
  uint64_t num_elements = heap_struct_addr[1] / 2;
  uint64_t padding = (2 + num_elements) % 2;
  uint64_t total_struct_size = (2 + num_elements + padding);
  for (int i = 0; i < total_struct_size; i++) {
    heap_top[i] = heap_struct_addr[i];
  }

#if LOG
  printf("number of elements for struct: %ld\n", num_elements);
#endif

  // Update the value at garter_val_addr with the value of heap_top.
  garter_val_addr = heap_top;

  // Replace the value at heap_thing_addr (i.e., the location referred to by
  // garter_val) with a forwarding pointer to heap_top.
  uint64_t ptr = ((uint64_t)heap_top) + PTR_TAG;
  *heap_struct_addr = ptr;

  // Increment heap_top as needed to record the allocation.
  heap_top += total_struct_size;

  // For each field within heap_thing at the new location, recursively call
  // copy_if_needed (Be careful about using the return value of those calls
  // correctly!)
  for (int i = 0; i < num_elements; i += 1) {
#if LOG
    printf("Index of struct element copying: %d - snakeval value: ", i);
    printHelp(stdout, garter_val_addr[i + 2]);
    printf("\n");
#endif
    heap_top = copy_if_needed(&garter_val_addr[i + 2], heap_top);
  }

#if LOG
  printf("returned heap_top in struct: %#018lx\n", (uint64_t)heap_top);
#endif

  // Return the current heap_top
  return heap_top;
}

/*
  Copies a tuple from its position on the current heap to the new heap

  Arguments:
    garter_val_addr: the address of the tagged tuple, contains the tagged tuple
    heap_top: the location to begin copying
*/
uint64_t *copy_tuple(uint64_t *garter_val_addr, uint64_t *heap_top) {
  SNAKEVAL garter_val = *garter_val_addr;
  uint64_t *heap_tuple_addr = (uint64_t *)(garter_val - TUPLE_TAG);
  if ((*heap_tuple_addr & PTR_TAG_MASK) == PTR_TAG) {
    // If garter_val is a (tagged) pointer to a heap_thing that now contains a
    // forwarding pointer, replace the value at garter_val_addr with the
    // appropriately tagged version of that forwarding pointer
    uint64_t *fw_ptr = (uint64_t *)(*heap_tuple_addr - PTR_TAG);
#if LOG
    printf("FWD PTR IN TUPLE!!!!!: %018lx\n", (uint64_t)fw_ptr);
#endif
    uint64_t retagged_fw_ptr = (uint64_t)fw_ptr + TUPLE_TAG;
    *garter_val_addr = retagged_fw_ptr;
    return heap_top;
  }

#if LOG
  printf("copying tuple: ");
  printHelp(stdout, garter_val);
  printf("\n");
#endif

  // Copy the full contents of heap_thing to heap_top
  uint64_t num_elements = heap_tuple_addr[0] / 2;
  uint64_t padding = (1 + num_elements) % 2;
  uint64_t total_tuple_size = (1 + num_elements + padding);
  for (int i = 0; i < total_tuple_size; i++) {
    heap_top[i] = heap_tuple_addr[i];
  }

#if LOG
  printf("number of elements for tuple: %ld\n", num_elements);
#endif

  // Update the value at garter_val_addr with the value of heap_top.
  garter_val_addr = heap_top;

  // Replace the value at heap_thing_addr (i.e., the location referred to by
  // garter_val) with a forwarding pointer to heap_top.
  uint64_t ptr = ((uint64_t)heap_top) + PTR_TAG;
  *heap_tuple_addr = ptr;

  // Increment heap_top as needed to record the allocation.
  // uint64_t *heap_top_saved = heap_top;
  heap_top += total_tuple_size;

  // For each field within heap_thing at the new location, recursively call
  // copy_if_needed (Be careful about using the return value of those calls
  // correctly!)
  for (int i = 0; i < num_elements; i += 1) {
#if LOG
    printf("Index of tuple element copying: %d - snakeval value: ", i);
    printHelp(stdout, garter_val_addr[i + 1]);
    printf("\n");
#endif
    heap_top = copy_if_needed(&garter_val_addr[i + 1], heap_top);
  }

#if LOG
  printf("returned heap_top in tuple: %#018lx\n", (uint64_t)heap_top);
#endif

  // Return the current heap_top
  return heap_top;
}

/*
  Copies a Garter value from the given address to the new heap,
  but only if the value is heap-allocated and needs copying.

  Arguments:
    garter_val_addr: the *address* of some Garter value, which contains a Garter
  value, i.e. a tagged word. It may or may not be a pointer to a heap-allocated
  value... heap_top: the location at which to begin copying, if any copying is
  needed

  Return value:
    The new top of the heap, at which to continue allocations

  Side effects:
    If the data needed to be copied, then this replaces the value at its old
  location with a forwarding pointer to its new location
 */
uint64_t *copy_if_needed(uint64_t *garter_val_addr, uint64_t *heap_top) {
  SNAKEVAL garter_val = *garter_val_addr;
#if LOG
  printf("value in copy_if_needed: %#018lx at %p\n", (uint64_t)garter_val,
         garter_val_addr);
#endif

  // Determine if the garter value is a pointer to a heap allocated garter val
  if (garter_val == NIL) {
    return heap_top;
  } else if ((garter_val & NUM_TAG_MASK) == NUM_TAG) {
    return heap_top;
  } else if ((garter_val == BOOL_TRUE) || (garter_val == BOOL_FALSE)) {
    return heap_top;
  } else if ((garter_val & STRUCT_TAG_MASK) == STRUCT_TAG && garter_val != STRUCT_TAG) {
    uint64_t *new_heap_top = copy_struct(garter_val_addr, heap_top);
    if (new_heap_top != heap_top) {
      uint64_t ptr = ((uint64_t)heap_top) + STRUCT_TAG;
      *garter_val_addr = ptr;
    }
    return new_heap_top;
  } else if ((garter_val & CLOSURE_TAG_MASK) == CLOSURE_TAG) {
    uint64_t *new_heap_top = copy_closure(garter_val_addr, heap_top);
    if (new_heap_top != heap_top) {
      uint64_t ptr = ((uint64_t)heap_top) + CLOSURE_TAG;
      *garter_val_addr = ptr;
    }
    return new_heap_top;
  } else if ((garter_val & TUPLE_TAG_MASK) == TUPLE_TAG) {
    uint64_t *new_heap_top = copy_tuple(garter_val_addr, heap_top);
    if (new_heap_top != heap_top) {
      uint64_t ptr = ((uint64_t)heap_top) + TUPLE_TAG;
      *garter_val_addr = ptr;
    }
    return new_heap_top;
  } else {
#if LOG
    printf("found garbage on the stack: %#018lx\n", garter_val);
#endif
    return heap_top;
  }
}

/*
  Implements Cheney's garbage collection algorithm.

  Arguments:
    bottom_frame: the base pointer of our_code_starts_here, i.e. the bottommost
  Garter frame top_frame: the base pointer of the topmost Garter stack frame
    top_stack: the current stack pointer of the topmost Garter stack frame
    from_start and from_end: bookend the from-space of memory that is being
  compacted to_start: the beginning of the to-space of memory

  Returns:
    The new location within to_start at which to allocate new data
 */
uint64_t *gc(uint64_t *bottom_frame, uint64_t *top_frame, uint64_t *top_stack,
             uint64_t *from_start, uint64_t *from_end, uint64_t *to_start) {

  uint64_t *old_top_frame = top_frame;
  do {
    for (uint64_t *cur_word = top_stack; cur_word < top_frame; cur_word++) {
#if LOG
      smarter_print_heap(from_start, from_end, 0, 0);
#endif
      to_start = copy_if_needed(cur_word, to_start);
#if LOG
      smarter_print_heap(0, 0, TO_S, TO_E);
#endif
    }
    /* Shift to next stack frame:
     * [top_frame] points to the saved RBP, which is the RBP of the next stack
     * frame, [top_frame + 8] is the return address, and [top_frame + 16] is
     * therefore the next frame's stack-top
     */
    top_stack = top_frame + 2;
    old_top_frame = top_frame;
    top_frame = (uint64_t *)(*top_frame);
    // NOTE: maybe do <=
  } while (old_top_frame < bottom_frame); // Use the old stack frame to decide
                                          // if there's more GC'ing to do

  // after copying and GC'ing all the stack frames, return the new allocation
  // starting point
  return to_start;
}
