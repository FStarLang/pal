#include "pal.h"
#include <stdint.h>

// Regression test for the `*p` emission bug on `_array T *` (PointerKind::Array).
// Previously, `*p` where `p` is a C array (decayed to a pointer) was emitted
// by PAL as Pulse `!p`, which is reference-deref and ill-typed because
// `array T` is not a `ref` (F* Error 189).
//
// The fix (src/pass/emit.rs, `ExprT::Deref` and `StmtT::Assign`-of-`Deref`)
// extends the existing `PointerKind::ArrayPtr` special case to also cover
// `PointerKind::Array`, emitting `array_read p 0sz` for reads and
// `array_write p 0sz v` for writes — semantically equivalent to `p[0]`
// and `p[0] = v`, which already worked.

// (1) `*p` read in an rvalue context (function body + post).
int deref_read(_array int *p)
  _requires(p._length >= 1)
  _preserves_value(p._length)
  _ensures(return == *p)
{
    return *p;
}

// (2) `*p = v` write through a decayed C array pointer.
void deref_write(_array int *p, int v)
  _requires(p._length >= 1)
  _preserves_value(p._length)
  _ensures(*p == v)
{
    *p = v;
}
