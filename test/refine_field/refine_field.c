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

/* An `_array` field's refinement is almost always about its length, and a
   length is not part of the field's value: the field holds an address, and the
   sequence behind it lives in the struct's ownership record. `this._length`
   therefore reads that record, which is the only place the length could come
   from -- the points-to predicate on purpose does not fix it. */
struct buf {
    _refine(this._length == 4) _array uint8_t *fixed;
};

uint8_t fourth(const struct buf *s) _requires(s->fixed._length == 4)
    _ensures(return == s->fixed[3])
{
    return s->fixed[3];
}

/* In Palow it is available to the *body* with no `_requires` of its own: the
   subscript's bounds obligation is discharged by the invariant alone. The old
   model does not carry a field's refinement that far, so there it has to be
   asked for again. */
uint8_t first(const struct buf *s)
#ifndef PALOW
    _requires(s->fixed._length == 4)
#endif
{
    return s->fixed[0];
}
