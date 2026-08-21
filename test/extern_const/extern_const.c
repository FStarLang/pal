// Test: the three shapes a file-scope object without a visible initializer can
// take, which mean three different things and must not be conflated.
//
//   extern const T x;   the value is real, fixed by another translation unit,
//                       and not knowable here -- so it is *assumed*
//   extern T x;         mutable storage owned by another translation unit --
//                       PAL has no model for it, so it is dropped
//   T x;                a tentative definition, which C zero-initializes --
//                       so its value really is the type's default
//
// The first is the interesting one. Emitting a *definition* for it would mean
// inventing a value, and inventing the type's default would let a proof
// conclude `limit == 0`, which nothing establishes: the definition in the other
// translation unit may say anything. So it is emitted as `assume val`, which
// lets a contract name it without claiming to know it.

#include "pal.h"

// Fixed elsewhere. We may name it, but may only reason about it through what a
// caller is told -- never by unfolding it to a literal.
extern const int limit;

// Mutable elsewhere, so dropped entirely. Declaring one must not stop the
// translation: this is the shape a macro-generated table declaration has.
extern int counter;

// Reads the assumed constant. Nothing here pins its value, so the postcondition
// can only relate the result to `limit` itself.
int get_limit(void)
  _ensures(return == limit)
{
    return limit;
}

// The assumed value flows through a contract like any other pure value: the
// caller has to establish the bound, because `limit` is not known to be small.
int under_limit(int n)
  _requires(n < limit)
  _ensures(return == n)
{
    return n;
}
