#include "pal.h"

/* Reading through a pointer stored in a struct: `o->pb->y`, where `pb` points
   at a `struct b` that points back at a `struct a`.

   The two models reach the second pointer by opposite routes. PAL's ownership
   of a struct is shallow -- a `struct a *` says nothing about what `pb`
   points at -- so the back-pointer has to be a `_core_ref` and the ownership
   behind it spelled out in a `_refine` on a separate typedef, written after
   both structs because folding it into `struct a`'s own predicate would make
   the two modules mutually dependent.

   Palow's ownership of a struct already reaches one level through its pointer
   fields: `struct_a_own` holds the `struct b` behind `pb`, so an ordinary
   parameter says everything the chain needs and the annotation has nothing
   left to add. `_core_ref` has no counterpart here and is not wanted; what it
   bought is what the generated ownership gives for free. */
#ifdef PALOW

struct b;
struct a { struct b *pb; int x; };
struct b { struct a *pa; int y; };

typedef struct a *a_owned;

#else

struct b;
struct a { _core_ref struct b *pb; int x; };
struct b {            struct a *pa; int y; };

_refine((_slprop) _inline_pulse(
  exists* (bv: $type(struct b)).
    pts_to (Pulse.Lib.C.CoreRef.core_to_ref $type(struct b)
              (($(*this)).$field(struct a::pb))) bv))
typedef struct a *a_owned;

#endif

/* Straight through, in one expression. */
int chained(a_owned o) // A
  _ensures(return == o->pb->y)
{
    return o->pb->y;
}

/* The same chain with the intermediate pointer parked in a local, which is
   where the ownership has to survive a statement boundary. */
int via_local(a_owned o) // B
  _ensures(return == o->pb->y)
{
    struct b *q = o->pb;
    return q->y;
}
