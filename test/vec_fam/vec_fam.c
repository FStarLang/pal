#include "pal.h"
#include <stdlib.h>
#include <stdint.h>

// A struct whose last field is a flexible array member (VLA in a struct). The
// `_refines` clause states that the length of the flexible array is always
// equal to the `len` field. PAL models `data` as an inline `array_spec` with
// no length pin; the refinement adds the `array_spec_len == len` relation to
// the struct predicate.
struct vec {
    unsigned len;
    _refines(this._length == len) int data[];
};

// Read an element of the flexible array. The precondition `i < v->len`, together
// with the `_refines` length relation carried by the struct predicate, lets the
// array read verify that `i` is in bounds. Preserving `i < v->len` keeps that
// bound in scope so the `v->data[i]` element postcondition is well-typed.
int vec_get(struct vec *v, unsigned i)
    _preserves(i < v->len)
    _ensures(return == v->data[i])
{
    return v->data[i];
}

// Write an element of the flexible array. Preserving `i < v->len` again keeps
// the index bound in scope for the `v->data[i]` element postcondition.
void vec_set(struct vec *v, unsigned i, int x)
    _preserves(i < v->len)
    _ensures(v->data[i] == x)
{
    v->data[i] = x;
}
