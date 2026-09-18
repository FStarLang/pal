#include "pal.h"
#include <stdint.h>

/* A `_refine` written on a *field* is an invariant of the struct type, not of
   any one object of it: every `struct box` anywhere has `0 < n < 100`. It
   therefore reaches a contract the way a struct-level `_refine` does -- by
   being stated for every parameter of the type -- with `this` standing for the
   field rather than for the whole struct. */
struct box {
    _refine(this > 0 && this < 100) int32_t n;
    int32_t m;
};

/* Through a pointer: `this` is the pointee's value projected at the field, so
   the clause is available at both ends of the contract for as long as the
   ownership is. */
int32_t read_through_pointer(const struct box *b) _ensures(return > 0)
{
    return b->n;
}

/* By value: there is no pointee, so `this` is the parameter itself projected
   at the field, and the clause is a precondition and nothing more -- a value
   parameter is immutable, so restating it on the way out would say nothing
   new. */
int32_t read_by_value(struct box b) _ensures(return > 0)
{
    return b.n;
}

/* The refinement is strong enough to discharge an overflow obligation that
   nothing else in the contract could: `n + n` is in range only because `n` is
   under 100. */
int32_t twice(const struct box *b) _ensures(return > 0)
{
    return b->n + b->n;
}

/* A second field with no refinement of its own, to check that the invariant is
   attached to the field it was written on and not to the struct. */
int32_t sum(const struct box *b) _requires(b->m > 0 && b->m < 100)
    _ensures(return > 0)
{
    return b->n + b->m;
}
