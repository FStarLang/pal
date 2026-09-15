#include "pal.h"
#include <stddef.h>
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
  let nonneg_offset (x: ptr) : slprop = pure (addr_of x >= 0)
)

// A nullable arrayptr carrying a refinement: unless_null wraps the whole prop
// produced by the inner type, including the refinement predicate, in a single
// unless_null.
void takes_nullable_refined(
    _nullable _refine(_inline_pulse(Nullable_include1.nonneg_offset $(this))) _arrayptr int *p) {}

// A nullable pointer to a struct.
struct ops { int32_t a; };
void takes_nullable_struct(_nullable const struct ops *p) {}

// A nullable function pointer.
typedef int (*binop)(int, int);
void takes_nullable_fnptr(_nullable binop f) {}

// Passing NULL to a _nullable parameter needs two ghost steps: the
// precondition is `unless_null p (...)`, and the intro is what turns `emp` into
// it -- Pulse cannot do that on its own, because which branch of the guard
// applies is decided by a pure fact rather than by the slprop's shape.
//
// Both arguments of the intro must be explicit, and the trailing elim is needed
// to release what the callee hands back. The second argument is the callee's
// precondition as printed in the generated module, with the guard stripped off.

void call_ref(void) {
    _ghost_stmt(intro_unless_null_null null (int32_t_pts_to null 1.0R 0l));
    takes_nullable_ref(NULL);
    _ghost_stmt(elim_unless_null_null null _);
}
// _array owns a sequence of elements, so the guarded predicate is array_pts_to.
void call_array(void) {
    _ghost_stmt(intro_unless_null_null null (array_pts_to int32_t_repr 4 null 1.0R (Seq.empty #Int32.t)));
    takes_nullable_array(NULL);
    _ghost_stmt(elim_unless_null_null null _);
}
// Palow has no separate _arrayptr, so this is the same shape as _array.
void call_arrayptr(void) {
    _ghost_stmt(intro_unless_null_null null (array_pts_to int32_t_repr 4 null 1.0R (Seq.empty #Int32.t)));
    takes_nullable_arrayptr(NULL);
    _ghost_stmt(elim_unless_null_null null _);
}
void call_struct(void) {
    _ghost_stmt(intro_unless_null_null null (struct_ops_pts_to null 1.0R ({ fld_a = 0l })));
    takes_nullable_struct(NULL);
    _ghost_stmt(elim_unless_null_null null _);
}
// A nullable function pointer owns nothing, so there is no guard to introduce.
void call_fnptr(void) {
    takes_nullable_fnptr(NULL);
}
