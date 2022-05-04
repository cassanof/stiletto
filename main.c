#include "gc.h"
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t SNAKEVAL;

extern SNAKEVAL
our_code_starts_here(uint64_t *HEAP,
                     uint64_t size) asm("?our_code_starts_here");
extern void error() asm("?error");
extern SNAKEVAL
set_stack_bottom(uint64_t *stack_bottom) asm("?set_stack_bottom");
extern uint64_t *get_heap_end() asm("?get_heap_end");
extern SNAKEVAL print(SNAKEVAL val) asm("?print");
extern SNAKEVAL input() asm("?input");
extern SNAKEVAL printStack(SNAKEVAL val, uint64_t *rsp, uint64_t *rbp,
                           uint64_t args) asm("?print_stack");
extern SNAKEVAL equal(SNAKEVAL val1, SNAKEVAL val2) asm("?equal");
extern SNAKEVAL testarg(SNAKEVAL a1, SNAKEVAL a2, SNAKEVAL a3, SNAKEVAL a4,
                        SNAKEVAL a5, SNAKEVAL a6, SNAKEVAL a7, SNAKEVAL a8,
                        SNAKEVAL a9) asm("?testarg");
extern uint64_t *try_gc(uint64_t *alloc_ptr, uint64_t amount_needed,
                        uint64_t *first_frame,
                        uint64_t *stack_top) asm("?try_gc");
extern uint64_t *HEAP_END asm("?HEAP_END");
extern uint64_t *HEAP asm("?HEAP");

const uint64_t NUM_TAG = 0x0000000000000000;
const uint64_t BOOL_TAG = 0x0000000000000007;
const uint64_t TUPLE_TAG = 0x0000000000000001;
const uint64_t CLOSURE_TAG = 0x0000000000000005;
const uint64_t STRUCT_TAG = 0x0000000000000003;
// NOTE: booleans and forwarding pointers share the same tag.
const uint64_t PTR_TAG = 0x0000000000000007;
const uint64_t BOOL_TRUE = 0xFFFFFFFFFFFFFFFF;
const uint64_t BOOL_FALSE = 0x7FFFFFFFFFFFFFFF;
const uint64_t NIL = ((uint64_t)NULL | TUPLE_TAG);

const uint64_t NUM_TAG_MASK = 0x0000000000000001;
const uint64_t BOOL_TAG_MASK = 0x0000000000000007;
const uint64_t TUPLE_TAG_MASK = 0x0000000000000007;
const uint64_t CLOSURE_TAG_MASK = 0x0000000000000007;
const uint64_t STRUCT_TAG_MASK = 0x0000000000000007;
const uint64_t PTR_TAG_MASK = 0x0000000000000007;

const uint64_t ERR_COMP_NOT_NUM = 1;
const uint64_t ERR_ARITH_NOT_NUM = 2;
const uint64_t ERR_LOGIC_NOT_BOOL = 3;
const uint64_t ERR_IF_NOT_BOOL = 4;
const uint64_t ERR_OVERFLOW = 5;
const uint64_t ERR_GET_NOT_TUPLE = 6;
const uint64_t ERR_GET_LOW_INDEX = 7;
const uint64_t ERR_GET_HIGH_INDEX = 8;
const uint64_t ERR_NIL_DEREF = 9;
const uint64_t ERR_OUT_OF_MEMORY = 10;
const uint64_t ERR_SET_NOT_TUPLE = 11;
const uint64_t ERR_SET_LOW_INDEX = 12;
const uint64_t ERR_SET_HIGH_INDEX = 13;
const uint64_t ERR_CALL_NOT_CLOSURE = 14;
const uint64_t ERR_CALL_ARITY_ERR = 15;
const uint64_t ERR_SET_NOT_NUM = 16;
const uint64_t ERR_GET_NOT_NUM = 17;
const uint64_t ERR_TUPLE_BAD_DESTRUCT = 18;
const uint64_t ERR_GETTER_NOT_STRUCT = 19;
const uint64_t ERR_SETTER_NOT_STRUCT = 20;
const uint64_t ERR_GETTER_FIELD_NOT_FOUND = 21;
const uint64_t ERR_SETTER_FIELD_NOT_FOUND = 22;
const uint64_t ERR_SETTER_FIELD_WRONG_STRUCT = 23;
const uint64_t ERR_CONSTRUCT_FIELD_WRONG_STRUCT = 24;

// 2^63 is 19 long. 1 more for null and one more for neg sign
const int BUFLEN = 21;

size_t HEAP_SIZE;
uint64_t *STACK_BOTTOM;
uint64_t *HEAP;
uint64_t *HEAP_END;

SNAKEVAL set_stack_bottom(uint64_t *stack_bottom) {
  STACK_BOTTOM = stack_bottom;
  return 0;
}

uint64_t *get_heap_end() { return HEAP_END; }

uint64_t *FROM_S;
uint64_t *FROM_E;
uint64_t *TO_S;
uint64_t *TO_E;

SNAKEVAL equal(SNAKEVAL val1, SNAKEVAL val2) {
  if (val1 == val2) {
    return BOOL_TRUE;
  }
  if (val1 == NIL || val2 == NIL) {
    return BOOL_FALSE;
  }
  if ((val1 & STRUCT_TAG_MASK) == STRUCT_TAG &&
      (val2 & STRUCT_TAG_MASK) == STRUCT_TAG) {
    uint64_t *stru1 = (uint64_t *)(val1 - STRUCT_TAG);
    uint64_t *stru2 = (uint64_t *)(val2 - STRUCT_TAG);

    if (stru1[0] != stru2[0] || stru1[1] != stru2[1]) {
      return BOOL_FALSE;
    }

    int strulen = stru1[1] / 2;

    // where 1 is check the field at index, and 0 is don't check the field
    int docheck[strulen];
    for (uint64_t i = 0; i < strulen; i++) {
      if ((stru1[i + 2] & CLOSURE_TAG_MASK) == CLOSURE_TAG) {
        docheck[i] = 0;
      } else {
        docheck[i] = 1;
      }
    }

    for (uint64_t i = 0; i < strulen; i++) {
      if (docheck[i] == 1 && equal(stru1[i + 2], stru2[i + 2]) == BOOL_FALSE)
        return BOOL_FALSE;
    }

    return BOOL_TRUE;
  }
  if ((val1 & TUPLE_TAG_MASK) == TUPLE_TAG &&
      (val2 & TUPLE_TAG_MASK) == TUPLE_TAG) {
    uint64_t *tup1 = (uint64_t *)(val1 - TUPLE_TAG);
    uint64_t *tup2 = (uint64_t *)(val2 - TUPLE_TAG);
    if (tup1[0] != tup2[0]) {
      return BOOL_FALSE;
    }

    for (uint64_t i = 1; i <= tup1[0] / 2; i++) {
      if (equal(tup1[i], tup2[i]) == BOOL_FALSE)
        return BOOL_FALSE;
    }
    return BOOL_TRUE;
  }
  return BOOL_FALSE;
}

uint64_t tupleCounter = 0;
uint64_t structCounter = 0;
// NOTE: for some reason, by default the length/arity values in lambdas/tuples
//       were snakevals
void printHelp(FILE *out, SNAKEVAL val) {
  if (val == NIL) {
    fprintf(out, "nil");
  } else if ((val & NUM_TAG_MASK) == NUM_TAG) {
    fprintf(out, "%ld",
            ((int64_t)val) >> 1); // deliberately int64, so that it's signed
  } else if (val == BOOL_TRUE) {
    fprintf(out, "true");
  } else if (val == BOOL_FALSE) {
    fprintf(out, "false");

  } else if ((val & STRUCT_TAG_MASK) == STRUCT_TAG && val != STRUCT_TAG) {
    // grab the address
    uint64_t *addr = (uint64_t *)(val - STRUCT_TAG);

    // Check whether we've visited this struct already
    if ((*addr & 0x8000000000000000) != 0) {
      fprintf(out, "<cyclic struct %d>", (int)(*addr - 0x7FFFFFFFFFFFFFFF));
      return;
    }

    uint64_t id = addr[0] / 2;
    uint64_t num_fields = addr[1] / 2;
    fprintf(out, "(Struct <%ld>: (", id);

    // tag struct
    *(addr) = 0x8000000000000000 | (++structCounter);
    for (int i = 0; i < num_fields; i++) {
      if ((addr[i + 2] & CLOSURE_TAG_MASK) == CLOSURE_TAG) {
        fprintf(out, "<closure field: %d>", i);
      } else {
        printHelp(out, addr[i + 2]);
      }
      if (i != num_fields - 1) {
        fprintf(out, ", ");
      }
    }

    // untag sttruct
    *(addr) = id * 2;

    fprintf(out, ") )");
  } else if ((val & CLOSURE_TAG_MASK) == CLOSURE_TAG) {
    // grab the address
    uint64_t *addr = (uint64_t *)(val - CLOSURE_TAG);
    uint64_t arity = addr[0] / 2;
    uint64_t num_vars = addr[2] / 2;

    fprintf(out, "(lambda (arity: %ld): ... ", arity);
    for (int i = 0; i < num_vars; i++) {
      if ((addr[i + 3] & CLOSURE_TAG_MASK) == CLOSURE_TAG) {
        fprintf(out, "<closure fv: %d>", i);
      } else if ((addr[i + 3] & STRUCT_TAG_MASK) == STRUCT_TAG) {
        fprintf(out, "<struct fv: %d>", i);
      } else {
        printHelp(out, addr[i + 3]);
      }
      printf(" ... ");
    }

    fprintf(out, ")");

  } else if ((val & TUPLE_TAG_MASK) == TUPLE_TAG) {
    uint64_t *addr = (uint64_t *)(val - TUPLE_TAG);
    // Check whether we've visited this tuple already
    if ((*addr & 0x8000000000000000) != 0) {
      fprintf(out, "<cyclic tuple %d>", (int)(*addr & 0x7FFFFFFFFFFFFFFF));
      return;
    }
    // Mark this tuple: save its length locally, then mark it
    uint64_t len = addr[0];
    if (len & 0x1) { // actually, it's a forwarding pointer
      fprintf(out, "actually forwarding to %#018lx", (uint64_t)(len - PTR_TAG));
      return;
    } else {
      len /= 2; // length is encoded
    }
    *(addr) = 0x8000000000000000 | (++tupleCounter);
    fprintf(out, "(");
    for (uint64_t i = 1; i <= len; i++) {
      if (i > 1)
        fprintf(out, ", ");
      printHelp(out, addr[i]);
    }
    if (len == 1)
      fprintf(out, ", ");
    fprintf(out, ")");
    // Unmark this tuple: restore its length
    *(addr) = len * 2; // length is encoded
  } else {
    fprintf(out, "Unknown value: %#018lx", val);
  }
}

SNAKEVAL printStack(SNAKEVAL val, uint64_t *rsp, uint64_t *rbp, uint64_t args) {
  printf("RSP: %#018lx\t==>  ", (uint64_t)rsp);
  fflush(stdout);
  printHelp(stdout, *rsp);
  fflush(stdout);
  printf("\nRBP: %#018lx\t==>  ", (uint64_t)rbp);
  fflush(stdout);
  printHelp(stdout, *rbp);
  fflush(stdout);
  printf("\n(difference: %ld)\n", (uint64_t)(rsp - rbp));
  fflush(stdout);
  printf("Requested return val: %#018lx\t==> ", (uint64_t)val);
  fflush(stdout);
  printHelp(stdout, val);
  fflush(stdout);
  printf("\n");
  fflush(stdout);
  printf("Num args: %ld\n", args);

  uint64_t *origRsp = rsp;

  for (uint64_t *cur = rsp; cur < STACK_BOTTOM + 3; cur++) {
    if (cur == STACK_BOTTOM) {
      printf("BOT %#018lx: %#018lx\t==>  old rbp\n", (uint64_t)cur, *cur);
      fflush(stdout);
    } else if (cur == rbp) {
      printf("RBP %#018lx: %#018lx\t==>  old rbp\n", (uint64_t)cur, *cur);
      fflush(stdout);
    } else if (cur == origRsp) {
      printf("    %#018lx: %#018lx\t==>  old rbp\n", (uint64_t)cur, *cur);
      fflush(stdout);
    } else if (cur == rbp + 1) {
      printf("    %#018lx: %#018lx\t==>  saved ret\n", (uint64_t)cur, *cur);
      fflush(stdout);
      rsp = rbp + 2;
      rbp = (uint64_t *)(*rbp);
    } else if (cur == STACK_BOTTOM + 2) {
      printf("    %#018lx: %#018lx\t==>  heap\n", (uint64_t)cur, *cur);
      fflush(stdout);
    } else {
      printf("    %#018lx: %#018lx\t==>  ", (uint64_t)cur, *cur);
      fflush(stdout);
      printHelp(stdout, *cur);
      fflush(stdout);
      printf("\n");
      fflush(stdout);
    }
  }
  return val;
}

// function to test native calls for 7 > args
SNAKEVAL testarg(SNAKEVAL a1, SNAKEVAL a2, SNAKEVAL a3, SNAKEVAL a4,
                 SNAKEVAL a5, SNAKEVAL a6, SNAKEVAL a7, SNAKEVAL a8,
                 SNAKEVAL a9) {
  print(a1);
  print(a2);
  print(a3);
  print(a4);
  print(a5);
  print(a6);
  print(a7);
  print(a8);
  print(a9);
  return BOOL_FALSE;
}

SNAKEVAL input() {
  char inputbuf[BUFLEN];
  fgets(inputbuf, BUFLEN, stdin);
  if (strcmp("true", inputbuf) == 0) {
    return BOOL_TRUE;
  }
  if (strcmp("false", inputbuf) == 0) {
    return BOOL_FALSE;
  }
  int64_t num = LONG_MAX; // dummy value that will fail if the input is bad
  if (sscanf(inputbuf, "%ld", &num) == 0 ||
      (num > (LONG_MAX / 2) || num < (LONG_MIN / 2))) {
    fprintf(stderr, "Input wasn't given a valid snakeval");
    exit(1);
  }
  return (SNAKEVAL)(num << 1);
}

SNAKEVAL print(SNAKEVAL val) {
  printHelp(stdout, val);
  printf("\n");
  fflush(stdout);
  return val;
}

void error(uint64_t code, SNAKEVAL val) {
  switch (code) {
  case ERR_COMP_NOT_NUM:
    fprintf(stderr, "Error: comparison expected a number, got ");
    printHelp(stderr, val);
    break;
  case ERR_ARITH_NOT_NUM:
    fprintf(stderr, "Error: arithmetic expected a number, got ");
    printHelp(stderr, val);
    break;
  case ERR_LOGIC_NOT_BOOL:
    fprintf(stderr, "Error: logic expected a boolean, got ");
    printHelp(stderr, val);
    break;
  case ERR_IF_NOT_BOOL:
    fprintf(stderr, "Error: if expected a boolean, got ");
    printHelp(stderr, val);
    break;
  case ERR_OVERFLOW:
    fprintf(stderr, "Error: Integer overflow, got ");
    printHelp(stderr, val);
    break;
  case ERR_GET_NOT_TUPLE:
    fprintf(stderr, "Error: get expected tuple");
    break;
  case ERR_GET_LOW_INDEX:
    fprintf(stderr, "Error: index too small to get, got %lu\n", (uint64_t)val);
    break;
  case ERR_GET_HIGH_INDEX:
    fprintf(stderr, "Error: index too large to get, got %lu\n", (uint64_t)val);
    break;
  case ERR_NIL_DEREF:
    fprintf(stderr, "Error: tried to access component of nil\n");
    break;
  case ERR_OUT_OF_MEMORY:
    fprintf(stderr, "Error: out of memory\n");
    break;
  case ERR_SET_NOT_TUPLE:
    fprintf(stderr, "Error: set expected tuple\n");
    break;
  case ERR_SET_LOW_INDEX:
    fprintf(stderr, "Error: index too small to set\n");
    break;
  case ERR_SET_HIGH_INDEX:
    fprintf(stderr, "Error: index too large to set\n");
    break;
  case ERR_CALL_NOT_CLOSURE:
    fprintf(stderr, "Error: tried to call a non-closure value: ");
    printHelp(stderr, val);
    break;
  case ERR_CALL_ARITY_ERR:
    fprintf(stderr, "Error: arity mismatch in call\n");
    break;
  case ERR_SET_NOT_NUM:
    fprintf(stderr, "Error: set expected numeric index\n");
    break;
  case ERR_GET_NOT_NUM:
    fprintf(stderr, "Error: get expected numeric index\n");
    break;
  case ERR_TUPLE_BAD_DESTRUCT:
    fprintf(stderr, "Error: a tuple was badly destructed\n");
    break;
  case ERR_GETTER_NOT_STRUCT:
    fprintf(stderr, "Error: a getter was given a non-struct value\n");
    break;
  case ERR_SETTER_NOT_STRUCT:
    fprintf(stderr, "Error: a setter was given a non-struct value\n");
    break;
  case ERR_GETTER_FIELD_NOT_FOUND:
    if ((val & NUM_TAG_MASK) == NUM_TAG && ((int64_t)val >> 1) == -1) {
      fprintf(stderr, "Error: a getter couldn't infer the type of a struct. "
                      "try type hints.");
    } else {
      fprintf(stderr, "Error: a getter couldn't find the field. got offset: ");
      printHelp(stderr, val);
    }
    break;
  case ERR_SETTER_FIELD_NOT_FOUND:
    if ((val & NUM_TAG_MASK) == NUM_TAG && ((int64_t)val >> 1) == -1) {
      fprintf(stderr, "Error: a setter couldn't infer the type of a struct. "
                      "try type hints.");
    } else {
      fprintf(stderr, "Error: a setter couldn't find the field. got offset: ");
      printHelp(stderr, val);
    }
    break;
  case ERR_SETTER_FIELD_WRONG_STRUCT:
    fprintf(stderr, "Error: a setter tried to set a struct field with a value "
                    "of a different type. struct: ");
    printHelp(stderr, val);
    break;
  case ERR_CONSTRUCT_FIELD_WRONG_STRUCT:
    fprintf(stderr, "Error: a constructor tried to set a struct field with a "
                    "value of a different type. struct: ");
    printHelp(stderr, val);
    break;
  default:
    fprintf(stderr, "Error: Unknown error code: %lu, val: ", code);
    printHelp(stderr, val);
  }
  fprintf(stderr, "\n%p ==> ", (uint64_t *)val);
  fflush(stderr);
  // naive_print_heap(HEAP, HEAP_END);
  fflush(stdout);
  free(HEAP);
  exit(code);
}

/*
  Try to reserve the desired number of bytes of memory, and free garbage if
  needed.  Fail (and exit the program) if there is insufficient memory.  Does
  not actually allocate the desired number of bytes of memory; the caller
  will do that.

  Arguments:

    uint64_t* alloc_ptr - the current top of the heap (which we store in R15),
  where the next allocation should occur, if possible uint64_t bytes_needed -
  the number of bytes of memory we want to allocate (including padding)
    uint64_t* cur_frame - the base pointer of the topmost stack frame of our
  code (i.e., RBP) uint64_t* cur_stack_top - the stack pointer of the topmost
  stack frame of our code (i.e., RSP)

  Returns:
    The new top of the heap (i.e. the new value of R15) after garbage
  collection. Does not actually allocate bytes_needed space.

  Side effect:
    Also updates HEAP_END to point to the new end of the heap, if it's changed
*/
uint64_t *try_gc(uint64_t *alloc_ptr, uint64_t bytes_needed,
                 uint64_t *cur_frame, uint64_t *cur_stack_top) {
  uint64_t *new_heap = (uint64_t *)calloc(HEAP_SIZE + 15, sizeof(uint64_t));
  uint64_t *old_heap = HEAP;
  uint64_t *old_heap_end = HEAP_END;

  uint64_t *new_r15 = (uint64_t *)(((uint64_t)new_heap + 15) & ~0xF);
  uint64_t *new_heap_end = new_r15 + HEAP_SIZE;

  FROM_S = (uint64_t *)(((uint64_t)HEAP + 15) & ~0xF);
  FROM_E = HEAP_END;
  TO_S = new_r15;
  TO_E = new_heap_end;

  // printf("FROM_S = %p, FROM_E = %p, TO_S = %p, TO_E = %p\n", FROM_S, FROM_E,
  //        TO_S, TO_E);
  // smarter_print_heap(FROM_S, FROM_E, TO_S, TO_E);
  // printStack(BOOL_TRUE, cur_stack_top, cur_frame, 0);

  // Abort early, if we can't allocate a new to-space
  if (new_heap == NULL) {
    fprintf(stderr, "Out of memory: could not allocate a new semispace for "
                    "garbage collection\n");
    fflush(stderr);
    if (old_heap != NULL)
      free(old_heap);
    exit(ERR_OUT_OF_MEMORY);
  }

  new_r15 =
      gc(STACK_BOTTOM, cur_frame, cur_stack_top, FROM_S, HEAP_END, new_r15);
  HEAP = new_heap;
  HEAP_END = new_heap_end;
  free(old_heap);

  // printf("new_r15 after gc: %#018llx\n", (uint64_t)new_r15);

  // Note: strict greater-than is correct here: if new_r15 + (bytes_needed / 8)
  // == HEAP_END, that does not mean we're *using* the byte at HEAP_END, but
  // rather that it would be the next free byte, which is still ok and not a
  // heap-overflow.
  // printf("bytes_needed/word_size: %lld - HEAP_SIZE: %zu\n",
  //        bytes_needed / sizeof(uint64_t), HEAP_SIZE);
  if (bytes_needed / sizeof(uint64_t) > HEAP_SIZE) {
    fprintf(
        stderr,
        "Allocation error: needed %ld words, but the heap is only %ld words\n",
        bytes_needed / sizeof(uint64_t), HEAP_SIZE);
    fflush(stderr);
    if (new_heap != NULL)
      free(new_heap);
    exit(ERR_OUT_OF_MEMORY);
  } else if ((new_r15 + (bytes_needed / sizeof(uint64_t))) > HEAP_END) {
    fprintf(stderr,
            "Out of memory: needed %ld words, but only %ld remain after "
            "collection\n",
            bytes_needed / sizeof(uint64_t), (HEAP_END - new_r15));
    fflush(stderr);
    if (new_heap != NULL)
      free(new_heap);
    exit(ERR_OUT_OF_MEMORY);
  } else {
    // fprintf(stderr, "new_r15 = %p\n", new_r15);
    // smarter_print_heap(HEAP, HEAP_END, new_heap, new_heap_end);
    return new_r15;
  }
}

int main(int argc, char **argv) {
  HEAP_SIZE = 100000;
  if (argc > 1) {
    HEAP_SIZE = atoi(argv[1]);
  }
  if (HEAP_SIZE < 0 || HEAP_SIZE > 1000000) {
    HEAP_SIZE = 0;
  }
  HEAP = (uint64_t *)calloc(HEAP_SIZE + 15, sizeof(uint64_t));

  uint64_t *aligned = (uint64_t *)(((uint64_t)HEAP + 15) & ~0xF);
  HEAP_END = aligned + HEAP_SIZE;
  // printf("HEAP = %p, aligned = %p, HEAP_END = %p\n", HEAP, aligned,
  // HEAP_END);
  SNAKEVAL result = our_code_starts_here(aligned, HEAP_SIZE);
  // smarter_print_heap(aligned, HEAP_END, TO_S, TO_E);
  print(result);

  free(HEAP);
  return 0;
}
