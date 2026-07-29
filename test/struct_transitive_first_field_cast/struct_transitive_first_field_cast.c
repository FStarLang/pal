// Test: casting between a struct pointer and a pointer to a TRANSITIVELY
// initial member -- the first field of the first field of ... -- in both
// directions and across more than two levels of nesting.
//
// C's initial-member rule (C17 6.7.2.1p17) applies recursively: if `x` is the
// first field of `in`, and `in` is the first field of `outer`, then `&o`,
// `&o->in`, and `&o->in.x` all denote one address. So `struct outer *` is
// interconvertible with `int32_t *` (two hops), and likewise across three or
// more hops.
//
// PAL lowers each direction to machinery it already emits, generalizing the
// single first-field hop to a chain of initial members:
//   struct -> deep-field ptr  `(int32_t *)o`      ==>  &o->in.x
//   deep-field ptr -> struct  `(struct outer *)q` ==>  _container_of(
//                                                        _container_of(q,
//                                                          struct inner, x),
//                                                        struct outer, in)
// A chain of length one is exactly the single first-field cast; here the chain
// has length two (outer/inner/int) and three (l1/l2/l3/int).
//
// The `roundtrip_via_*` functions at the bottom cast out to a deep field and
// back within a single function. There, ownership enters named on the original
// pointer but the write goes through the recovered `container`-nested pointer,
// which is provably equal to the original (per-level `*_container_inv` lemmas)
// yet is not unified by the Pulse frame matcher. A ghost `readdr_*` bridge --
// expressed purely in PAL annotations, exactly as in test/container_field_read
// -- re-addresses the touched cells across that equality; PAL is unchanged.

#include "pal.h"
#include <stdint.h>

// --- Two levels: outer -> inner -> int32_t ---------------------------------

struct inner {
    int32_t x;   // innermost initial member (offset 0)
    int32_t y;
};

struct outer {
    struct inner in;   // first field: itself a struct (offset 0)
    int32_t tag;
};

// struct -> deep-field pointer (2 hops): `(int32_t *)o` recovers &o->in.x.
// Write the innermost field through the recovered pointer; ownership of the
// fields comes from the default struct predicate in the contract.
void set_deep_via_cast(struct outer *o, int32_t v)
    _ensures(o->in.x == v)
{
    int32_t *q = (int32_t *)o;
    *q = v;
}

// struct -> deep-field pointer, read direction (2 hops): `(int32_t *)o`
// == &o->in.x.
int32_t get_deep_via_cast(struct outer *o)
    _ensures(return == o->in.x)
{
    int32_t *q = (int32_t *)o;
    return *q;
}

// deep-field pointer -> struct (2 hops): `(struct outer *)q` recovers the
// enclosing `outer` from a pointer to its innermost field, then reads a
// sibling. Ownership of the whole outer reachable through `q` is named with
// the same nested `_container_of` the cast lowers to, so the frame matcher
// unifies it syntactically.
int32_t read_tag_via_cast(_plain int32_t *q)
    _preserves(_inline_pulse(
      exists* (ov: $type(struct outer)).
        pts_to $(_container_of(_container_of(q, struct inner, x),
                               struct outer, in)) #1.0R ov **
        Struct_outer.struct_outer__pred
          (!$(_container_of(_container_of(q, struct inner, x),
                            struct outer, in))) 1.0R))
    _ensures(_inline_pulse(
      pure ($(return) ==
        !(Struct_outer.struct_outer__get_tag
            $(_container_of(_container_of(q, struct inner, x),
                            struct outer, in))))))
{
    struct outer *o = (struct outer *)q;
    return o->tag;
}

// --- Three levels: l1 -> l2 -> l3 -> int32_t (more than two hops) -----------

struct l3 {
    int32_t a;   // innermost initial member (offset 0)
    int32_t b;
};

struct l2 {
    struct l3 c;   // first field
    int32_t m;
};

struct l1 {
    struct l2 d;   // first field
    int32_t n;
};

// struct -> deep-field pointer (3 hops): `(int32_t *)p` recovers &p->d.c.a.
void set_deepest_via_cast(struct l1 *p, int32_t v)
    _ensures(p->d.c.a == v)
{
    int32_t *q = (int32_t *)p;
    *q = v;
}

// deep-field pointer -> struct (3 hops): recover `l1` from a pointer to its
// innermost field &p->d.c.a and read the outermost sibling `n`.
int32_t read_n_via_cast(_plain int32_t *q)
    _preserves(_inline_pulse(
      exists* (pv: $type(struct l1)).
        pts_to $(_container_of(_container_of(_container_of(q, struct l3, a),
                               struct l2, c), struct l1, d)) #1.0R pv **
        Struct_l1.struct_l1__pred
          (!$(_container_of(_container_of(_container_of(q, struct l3, a),
                            struct l2, c), struct l1, d))) 1.0R))
    _ensures(_inline_pulse(
      pure ($(return) ==
        !(Struct_l1.struct_l1__get_n
            $(_container_of(_container_of(_container_of(q, struct l3, a),
                            struct l2, c), struct l1, d))))))
{
    struct l1 *p = (struct l1 *)q;
    return p->n;
}

// --- Single-function round-trips: cast out to a deep field and back ---------
//
// Each function casts `struct * -> int32_t * -> struct *`, writes a sibling
// field through the recovered pointer, and reads it back through the original.
// Ownership enters named on the original pointer `o`, but the write goes
// through `o2`, which the cast lowers to the nested container projection
// `_container_of(_container_of(q, struct inner, x), struct outer, in)`. That
// expression equals `o` by the emitted per-level `*_container_inv` right-inverse
// lemmas, but the Pulse frame matcher does not fire those SMTPats on its own, so
// it cannot locate the cells addressed through `o2`. The ghost `readdr_*`
// bridges re-address the two cells the write touches (the raw-unfolded witness
// and the target field) from `o` to `o2` and back; their residual ref-equality
// goal is closed by those lemmas. This is the same move as
// test/container_field_read, expressed only in PAL annotations.

_include_pulse(Roundtrip_include,
  module SO = Struct_outer
  module L1 = Struct_l1

  // Re-address the raw-unfolded witness and the `tag` cell of a `struct outer`
  // from `a` to `b` when they denote the same object (`a == b`, discharged at
  // the call site by the outer/inner `*_container_inv` SMTPats).
  ghost fn readdr_outer (a: $type(struct outer *)) (b: $type(struct outer *))
                        (#tv: $type(int32_t))
    requires
      (SO.struct_outer__aux_raw_unfolded a 1.0R **
       pts_to (SO.struct_outer__tag_1 a) #1.0R tv **
       pure (a == b))
    ensures
      (SO.struct_outer__aux_raw_unfolded b 1.0R **
       pts_to (SO.struct_outer__tag_1 b) #1.0R tv)
  {
    rewrite (SO.struct_outer__aux_raw_unfolded a 1.0R)
         as (SO.struct_outer__aux_raw_unfolded b 1.0R);
    rewrite (pts_to (SO.struct_outer__tag_1 a) #1.0R tv)
         as (pts_to (SO.struct_outer__tag_1 b) #1.0R tv);
  }

  // Same, for a `struct l1` and its `n` cell (three nesting levels).
  ghost fn readdr_l1 (a: $type(struct l1 *)) (b: $type(struct l1 *))
                     (#tv: $type(int32_t))
    requires
      (L1.struct_l1__aux_raw_unfolded a 1.0R **
       pts_to (L1.struct_l1__n_1 a) #1.0R tv **
       pure (a == b))
    ensures
      (L1.struct_l1__aux_raw_unfolded b 1.0R **
       pts_to (L1.struct_l1__n_1 b) #1.0R tv)
  {
    rewrite (L1.struct_l1__aux_raw_unfolded a 1.0R)
         as (L1.struct_l1__aux_raw_unfolded b 1.0R);
    rewrite (pts_to (L1.struct_l1__n_1 a) #1.0R tv)
         as (pts_to (L1.struct_l1__n_1 b) #1.0R tv);
  }
)

// Round trip through two hops: cast `outer *` to a pointer to the innermost
// field, cast that back to `outer *`, write `tag` through the recovered
// pointer, then read it back through the original one.
int32_t roundtrip_via_2hop(struct outer *o, int32_t v)
    _ensures(return == v)
{
    int32_t *q = (int32_t *)o;
    struct outer *o2 = (struct outer *)q;
    _ghost_stmt(Roundtrip_include.readdr_outer $(o) $(o2));
    o2->tag = v;
    _ghost_stmt(Roundtrip_include.readdr_outer $(o2) $(o));
    return o->tag;
}

// Round trip through three hops.
int32_t roundtrip_via_3hop(struct l1 *p, int32_t v)
    _ensures(return == v)
{
    int32_t *q = (int32_t *)p;
    struct l1 *p2 = (struct l1 *)q;
    _ghost_stmt(Roundtrip_include.readdr_l1 $(p) $(p2));
    p2->n = v;
    _ghost_stmt(Roundtrip_include.readdr_l1 $(p2) $(p));
    return p->n;
}
