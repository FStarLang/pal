#include "pal.h"

struct b;
struct a { _core_ref struct b *pb; int x; };
struct b {            struct a *pa; int y; };

// `struct a *` refined with ownership of the struct b reached through the
// core_ref `pb` back-pointer. Defined after both structs, as a separate
// typedef -- folding this into struct a's own predicate instead would make
// Struct_a depend on Struct_b, which already depends on Struct_a (via `pa`),
// a cycle (F* Error 308).
_refine((_slprop) _inline_pulse(
  exists* (bv: $type(struct b)).
    pts_to (Pulse.Lib.C.CoreRef.core_to_ref $type(struct b)
              (($(*this)).$field(struct a::pb))) bv))
typedef struct a *a_owned;

int chained(a_owned o) // A
  _ensures(return == o->pb->y)
{
    return o->pb->y;
}

int via_local(a_owned o) // B
  _ensures(return == o->pb->y)
{
    struct b *q = o->pb;
    return q->y;
}
