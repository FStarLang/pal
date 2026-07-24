#include "pal.h"
#include <stddef.h>

// Regression test for the `arrayptr_diff` soundness fix.
//
// In C, pointer subtraction `p - q` is only defined when both operands point
// into the *same* array object (C11 6.5.6p9); doing it across two distinct
// objects is undefined behavior. Before the fix, `arrayptr_diff` lacked the
// `requires base_of x == base_of z` precondition that its sibling comparison
// operators (`arrayptr_lt`/`arrayptr_lte`) already carried, so PAL happily
// "verified" cross-object subtraction as safe.
//
// This positive test exercises the *legitimate* case: subtracting two pointers
// derived from the SAME array. It must still verify after the fix -- both
// pointers share `a`'s base, and the offset difference (7 - 2 == 5) trivially
// fits `ptrdiff_t`.
ptrdiff_t same_object_diff(_array int *a)
  _requires(a._length == 10)
{
  _arrayptr int *p = a + 7;
  _arrayptr int *q = a + 2;
  ptrdiff_t d = p - q;   // well-defined: p, q point into the same object
  _ghost_stmt(arrayptr_drop $(p));
  _ghost_stmt(arrayptr_drop $(q));
  return d;
}
