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
