#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

/*
  Prints the contents of the heap, in terms of the word number, the exact address, 
  the hex value at that address and the decimal value at that address.  Does not
  attempt to interpret the words as Garter values

  Arguments:
    heap: the starting address of the heap
    heap_end: the first address after the heap
 */
void naive_print_heap(uint64_t* heap, uint64_t* heap_end) asm("?naive_print_heap");

// IMPLEMENT THE FUNCTIONS BELOW

/*
  Smarter algorithm to print the contents of the heap.  You should implement this function
  much like the naive approach above, but try to have it print out values as Garter values

  Arguments:
    from_start: the starting address (inclusive) of the from-space of the heap
    from_end: the ending address (exclusive) of the from-space of the heap
    to_start: the starting address (inclusive) of the to-space of the heap
    to_end: the ending address (exclusive) of the to-space of the heap
 */
void smarter_print_heap(uint64_t* from_start, uint64_t* from_end, uint64_t* to_start, uint64_t* to_end);

/*
  Copies a Garter value from the given address to the new heap, 
  but only if the value is heap-allocated and needs copying.

  Arguments:
    garter_val_addr: the *address* of some Garter value, which contains a Garter value, 
                     i.e. a tagged word.  
                     It may or may not be a pointer to a heap-allocated value...
    heap_top: the location at which to begin copying, if any copying is needed

  Return value:
    The new top of the heap, at which to continue allocations

  Side effects:
    If the data needed to be copied, then this replaces the value at its old location 
    with a forwarding pointer to its new location
 */
uint64_t* copy_if_needed(uint64_t* garter_val_addr, uint64_t* heap_top);

/*
  Implements Cheney's garbage collection algorithm.

  Arguments:
    bottom_frame: the base pointer of our_code_starts_here, i.e. the bottommost Garter frame
    top_frame: the base pointer of the topmost Garter stack frame
    top_stack: the current stack pointer of the topmost Garter stack frame
    from_start and from_end: bookend the from-space of memory that is being compacted
    to_start: the beginning of the to-space of memory

  Returns:
    The new location within to_start at which to allocate new data
 */
uint64_t* gc(uint64_t* bottom_frame, uint64_t* top_frame, uint64_t* top_stack, uint64_t* from_start, uint64_t* from_end, uint64_t* to_start);
