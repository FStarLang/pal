// A `_refine` on a parameter that is not a pointer.
//
// The refinement is a claim about the value itself -- `this` is the parameter,
// not storage it points at -- so it is a precondition and nothing more: a
// value parameter is immutable, and restating it on the way out would add
// nothing the caller could not already derive.
//
// Palow used to drop such a refinement without a word, because it collected
// refinements only while walking a parameter's pointee, and a parameter with
// no pointee never reached the collection. The refinements below are load
// bearing: without them none of these bodies can be shown not to overflow.

#include "pal.h"
#include <stdint.h>

typedef int32_t _refine(this > 0 && this < 100) small;

int32_t double_it(small x)
  _ensures(return > 0)
{
    return x + x;
}

// Two refined parameters, so the two clauses have to be kept apart.
int32_t sum(small x, small y)
  _ensures(return > 0)
{
    return x + y;
}

// A refinement on one parameter and ownership on another: the refinement is a
// precondition, the points-to is ownership, and the two land in the same
// `requires` without interfering.
void scale(int32_t *p, small k)
  _requires(*p >= 0 && *p < 100)
{
    *p = *p * k;
}
