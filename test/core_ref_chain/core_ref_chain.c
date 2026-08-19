#include "pal.h"

struct b;
struct a { _core_ref struct b *pb; int x; };
struct b {            struct a *pa; int y; };

int chained(struct a *o)   { return o->pb->y; }                    // A

int via_local(struct a *o) // B
  _requires(_inline_pulse(
    exists* (bv: $type(struct b)).
      pts_to (Pulse.Lib.C.CoreRef.core_to_ref $type(struct b)
                ($(*o)).$field(struct a::pb)) bv))
  _ensures(_inline_pulse(
    exists* (bv: $type(struct b)).
      pts_to (Pulse.Lib.C.CoreRef.core_to_ref $type(struct b)
                ($(*o)).$field(struct a::pb)) bv))
{
    struct b *q = o->pb;
    return q->y;
}
