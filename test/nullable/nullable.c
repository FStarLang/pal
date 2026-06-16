#include "pal.h"
#include <stdint.h>

// A nullable array parameter: the pts_to is wrapped in unless_null, so passing
// a null pointer is allowed (the resource collapses to emp).
void takes_nullable_array(_nullable _array int *a) {}

// A nullable reference parameter.
void takes_nullable_ref(_nullable int *r) {}

// A nullable arrayptr: _arrayptr emits no pts_to of its own, so this is just
// unless_null this emp.
void takes_nullable_arrayptr(_nullable _arrayptr int *p) {}

_include_pulse(Nullable_include1,
  // A user-defined predicate over a pointer, as in pred(this).
  let nonneg_offset #a (x: array a) : slprop = pure (offset_of x >= 0)
)

// A nullable arrayptr carrying a refinement: unless_null wraps the whole prop
// produced by the inner type, including the refinement predicate, in a single
// unless_null.
void takes_nullable_refined(
    _nullable _refine(_inline_pulse(Nullable_include1.nonneg_offset $(this))) _arrayptr int *p) {}
