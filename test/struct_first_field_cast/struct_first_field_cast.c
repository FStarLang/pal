// Test: casting between a struct pointer and a pointer to its FIRST field,
// in both directions.
//
// This is legal in C only for the initial member (C17 6.7.2.1p17): "A pointer
// to a structure object, suitably converted, points to its initial member ...
// and vice versa. There may be unnamed padding within a structure object, but
// not at its beginning."
//
// PAL lowers the two directions to machinery it already emits:
//   struct -> first-field ptr  `(F *)s`        ==>  &s->firstfield
//   first-field ptr -> struct  `(struct S *)p` ==>  _container_of(p, S, first)
//
// Neither surface form needs the generated F* symbols spelled by hand; the
// field->struct spec reuses the `_container_of` intrinsic, which produces the
// same node the cast does.

#include "pal.h"
#include <stdint.h>

struct pair {
    int32_t first;   // first field (offset 0)
    int32_t second;
};

// struct -> first-field pointer: `(int32_t *)p` recovers &p->first. Write the
// first field through the recovered pointer; ownership of the fields comes from
// the default struct predicate in the contract.
void set_first_via_cast(struct pair *p, int32_t v)
    _ensures(_inline_pulse(
      pure (!(Struct_pair.struct_pair__get_first $(p)) == $(v))))
{
    int32_t *q = (int32_t *)p;
    *q = v;
}

// struct -> first-field pointer, read direction: `(int32_t *)p` == &p->first.
int32_t get_first_via_cast(struct pair *p)
    _ensures(_inline_pulse(
      pure ($(return) == !(Struct_pair.struct_pair__get_first $(p)))))
{
    int32_t *q = (int32_t *)p;
    return *q;
}

// first-field pointer -> struct: `(struct pair *)q` recovers the enclosing
// pair from a pointer to its first field, then reads a sibling field. Ownership
// of the whole pair reachable through `q` is required and handed back, named in
// the spec with the same `_container_of` intrinsic the cast lowers to.
int32_t read_second_via_cast(_plain int32_t *q)
    _preserves(_inline_pulse(
      exists* (pv: $type(struct pair)).
        pts_to $(_container_of(q, struct pair, first)) #1.0R pv **
        Struct_pair.struct_pair__pred
          (!$(_container_of(q, struct pair, first))) 1.0R))
    _ensures(_inline_pulse(
      pure ($(return) ==
        !(Struct_pair.struct_pair__get_second
            $(_container_of(q, struct pair, first))))))
{
    struct pair *p = (struct pair *)q;
    return p->second;
}

// ---------------------------------------------------------------------------
// First field is another (anonymous) struct.
//
// The embedded aggregate is defined without a struct tag and named only
// through a typedef, so the pointer cast can still spell its type. Casting the
// outer pointer yields a pointer to this initial member, and casting such a
// member pointer back recovers the outer struct.

typedef struct {
    int32_t x;
    int32_t y;
} point_t;

struct boxed_point {
    point_t p;      // first field: an anonymous struct
    int32_t label;
};

// struct -> first-field pointer, where the first field is the anonymous struct:
// `(point_t *)b` recovers &b->p. Write the embedded struct's subfields through
// the recovered pointer.
void set_point_via_cast(struct boxed_point *b, int32_t nx, int32_t ny)
    _ensures(b->p.x == nx)
    _ensures(b->p.y == ny)
{
    point_t *pp = (point_t *)b;
    pp->x = nx;
    pp->y = ny;
}

// first-field(anonymous struct) pointer -> struct: `(struct boxed_point *)pp`
// recovers the enclosing boxed_point from a pointer to its embedded point, then
// reads the sibling `label`.
int32_t label_via_cast(_plain point_t *pp)
    _preserves(_inline_pulse(
      exists* (bv: $type(struct boxed_point)).
        pts_to $(_container_of(pp, struct boxed_point, p)) #1.0R bv **
        Struct_boxed_point.struct_boxed_point__pred
          (!$(_container_of(pp, struct boxed_point, p))) 1.0R))
    _ensures(_inline_pulse(
      pure ($(return) ==
        !(Struct_boxed_point.struct_boxed_point__get_label
            $(_container_of(pp, struct boxed_point, p))))))
{
    struct boxed_point *b = (struct boxed_point *)pp;
    return b->label;
}
