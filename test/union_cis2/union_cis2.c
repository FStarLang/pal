#include "pal.h"

// FEATURE: casting a struct whose FIRST FIELD is a common-initial-sequence
// (CIS) union to that union's NAMED arm pointer type. The union has an
// anonymous arm and a named, tagged arm with identical layout:
//
//     union {
//         struct { int a; int b; };   // anonymous arm: h->a / h->b
//         struct list list;           // named, tagged arm
//     };
//
// letting code read the members directly AND obtain a `struct list *` view of
// the leading pair via `(struct list *) h`.
//
// PAL support: the frontend lowers `(struct list *)h` to `&h->list` (the named
// arm is at offset 0), and elim_cis collapses the byte-identical CIS union so
// `struct list` becomes the leading member. The cast view thus aliases the CIS
// leading slot `h->a`. Each function writes `v` and reads it back -- crossing
// between the cast view and the anonymous arm -- so `_ensures(return == v)`
// proves the two denote the same storage.

struct list { int a; int b; };

struct head {
    union {
        struct { int a; int b; };   // anonymous arm  -> h->a / h->b
        struct list list;           // named, tagged arm -> h->list.a / &h->list
    };
    int qlen;
};

// Write through the cast pointer, read back through the anonymous arm.
int write_via_cast(struct head *h, int v)
    _ensures(return == v)
{
    struct list *l = (struct list *)h;
    l->a = v;
    return h->a;
}

// Write through the anonymous arm, read back through the cast pointer.
int read_via_cast(struct head *h, int v)
    _ensures(return == v)
{
    h->a = v;
    struct list *l = (struct list *)h;
    return l->a;
}

// Write and read entirely through the cast pointer.
int roundtrip_via_cast(struct head *h, int v)
    _ensures(return == v)
{
    struct list *l = (struct list *)h;
    l->a = v;
    return l->a;
}

// Cast a pointer to the leading CIS field back to the enclosing struct pointer.
// The `struct list *` view is obtained from a genuine `struct head`, so casting
// it back to `struct head *` recovers the original object -- including the
// trailing `qlen`, which lives beyond the leading CIS field. PAL lowers the
// reverse cast `(struct head *)l` to the per-field container-of projection
// `struct_head___unnamed0_container` (the inverse of the forward
// `(struct list *)h -> &h->list` lowering); the emitted `_container_inv` SMTPat
// proves the recovered pointer equals `h`, so writing `qlen` through it and
// reading it back through `h` denote the same storage.
//
// Recovering the enclosing struct yields the ref in its container-projected
// form `container(unnamed0_1 h)`. That is provably equal to `h`, but the Pulse
// frame matcher will not fire the `_container_inv` SMTPat on its own to
// re-address the whole-struct ownership (`aux_raw_unfolded` + the `qlen` cell)
// from the `h` form to the `container(...)` form. The two ghost bridges below
// steer that rewrite (their residual ref-equality goal is discharged by the
// lemma), matching the pattern in test/container_field_read.
_include_pulse(Union_cis2_include,
  module H = Struct_head

  // Re-address the whole-struct ownership from the `h` form to the
  // container-projected form the recovered pointer carries.
  ghost fn to_container (h: $type(struct head *)) (#qv: $type(int))
    requires
      (H.struct_head__aux_raw_unfolded h 1.0R) **
      (pts_to (H.struct_head__qlen_1 h) qv)
    ensures
      (H.struct_head__aux_raw_unfolded
         (H.struct_head___unnamed0_container (H.struct_head___unnamed0_1 h)) 1.0R) **
      (pts_to (H.struct_head__qlen_1
         (H.struct_head___unnamed0_container (H.struct_head___unnamed0_1 h))) qv)
  {
    rewrite (H.struct_head__aux_raw_unfolded h 1.0R)
         as (H.struct_head__aux_raw_unfolded
              (H.struct_head___unnamed0_container (H.struct_head___unnamed0_1 h)) 1.0R);
    rewrite (pts_to (H.struct_head__qlen_1 h) qv)
         as (pts_to (H.struct_head__qlen_1
              (H.struct_head___unnamed0_container (H.struct_head___unnamed0_1 h))) qv);
  }

  // Re-address it back, restoring the caller's `h`-named ownership.
  ghost fn from_container (h: $type(struct head *)) (#qv: $type(int))
    requires
      (H.struct_head__aux_raw_unfolded
         (H.struct_head___unnamed0_container (H.struct_head___unnamed0_1 h)) 1.0R) **
      (pts_to (H.struct_head__qlen_1
         (H.struct_head___unnamed0_container (H.struct_head___unnamed0_1 h))) qv)
    ensures
      (H.struct_head__aux_raw_unfolded h 1.0R) **
      (pts_to (H.struct_head__qlen_1 h) qv)
  {
    rewrite (H.struct_head__aux_raw_unfolded
              (H.struct_head___unnamed0_container (H.struct_head___unnamed0_1 h)) 1.0R)
         as (H.struct_head__aux_raw_unfolded h 1.0R);
    rewrite (pts_to (H.struct_head__qlen_1
              (H.struct_head___unnamed0_container (H.struct_head___unnamed0_1 h))) qv)
         as (pts_to (H.struct_head__qlen_1 h) qv);
  }
)

int cast_field_to_struct(struct head *h, int v)
    _ensures(return == v)
{
    struct list *l = (struct list *)h;   // view of the leading CIS field
    struct head *h2 = (struct head *)l;  // cast back to the enclosing struct
    _ghost_stmt(Union_cis2_include.to_container $(h));
    h2->qlen = v;
    _ghost_stmt(Union_cis2_include.from_container $(h));
    return h->qlen;
}
