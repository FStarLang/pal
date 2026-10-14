// Test: a parameter whose `const` says nothing about ownership stays Regular.
//
// A `const` parameter is normally a borrow: PAL makes its permission and its
// pointee signature-level implicits, so that a `_preserves` clause can hand
// the caller's own hold straight back. That only works when the parameter has
// ownership to speak of. Two kinds do not, and for them the implicit appears
// nowhere but in `emp`, so no call site can ever solve it and the call does
// not elaborate:
//
//   - a scalar passed by value, where the top-level `const` only forbids
//     reassigning the callee's own copy, and
//   - a `_core_ref`, which is an address with no `pts_to` at all.
//
// Each callee below is exercised through a caller, because the failure is at
// the call site: the callee alone type-checks either way.

#include "pal.h"
#include <stdint.h>

struct thing {
    uint32_t field;
};

/* By-value scalars. The pointer parameter is a genuine borrow and must stay
 * one; the two scalars must not become borrows just because they are const. */
void by_value(const uint64_t count, const uint32_t width, const struct thing *t)
{
    uint64_t total = count + (uint64_t)width;
}

void call_by_value(const struct thing *t)
{
    by_value(7, 3, t);
}

/* A `_core_ref` parameter, both spelled directly and reached through a
 * typedef -- which is how it has to be written to land on the pointee of a
 * `void const **` out-parameter. */
typedef _core_ref void const *core_cptr;

void by_core_ref(_core_ref struct thing const *direct, core_cptr through_typedef)
{
}

void call_by_core_ref(const struct thing *t)
{
    by_core_ref(t, t);
}
