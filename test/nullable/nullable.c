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
  let nonneg_offset #a (x: array a) : slprop = pure (offset_of x >= 0)
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

// Passing NULL to a _nullable parameter needs two ghost steps: the precondition
// is `unless_null p (...)`, and Pulse cannot introduce it on its own because
// `has_is_null` is still a uvar at match time. Naming the pointer type fixes it.
//
// Both arguments of the intro must be explicit, and the trailing elim is needed
// to release what the callee hands back. `p` is the callee's precondition as
// printed in the generated .fsti, minus any [@@pulse_eager_unfold] predicate
// that reduces to emp (writing those out breaks the match).

void call_ref(void) {
    _ghost_stmt(Pulse.Lib.C.Nullable.intro_unless_null_null (null #Int32.t) (Pulse.Lib.Reference.pts_to (null #Int32.t) #1.0R 0l));
    takes_nullable_ref(NULL);
    _ghost_stmt(Pulse.Lib.C.Nullable.elim_unless_null_null (null #Int32.t) _);
}
// _array needs array_pts_to_full and a concrete full_array_spec.
void call_array(void) {
    _ghost_stmt(Pulse.Lib.C.Nullable.intro_unless_null_null (array_null #Int32.t) (array_pts_to_full (array_null #Int32.t) 1.0R (array_spec_zeroed Int32.t 0 0l)));
    takes_nullable_array(NULL);
    _ghost_stmt(Pulse.Lib.C.Nullable.elim_unless_null_null (array_null #Int32.t) _);
}
// _arrayptr emits no pts_to of its own, so p is emp.
void call_arrayptr(void) {
    _ghost_stmt(Pulse.Lib.C.Nullable.intro_unless_null_null (array_null #Int32.t) emp);
    takes_nullable_arrayptr(NULL);
    _ghost_stmt(Pulse.Lib.C.Nullable.elim_unless_null_null (array_null #Int32.t) _);
}
// A refinement rides inside the same unless_null, so p is the refinement.
void call_refined(void) {
    _ghost_stmt(Pulse.Lib.C.Nullable.intro_unless_null_null (array_null #Int32.t) (Nullable_include1.nonneg_offset (array_null #Int32.t)));
    takes_nullable_refined(NULL);
    _ghost_stmt(Pulse.Lib.C.Nullable.elim_unless_null_null (array_null #Int32.t) _);
}
void call_struct(void) {
    _ghost_stmt(Pulse.Lib.C.Nullable.intro_unless_null_null (null #Struct_ops.struct_ops) (Pulse.Lib.Reference.pts_to (null #Struct_ops.struct_ops) #1.0R (Struct_ops.Mkstruct_ops 0l)));
    takes_nullable_struct(NULL);
    _ghost_stmt(Pulse.Lib.C.Nullable.elim_unless_null_null (null #Struct_ops.struct_ops) _);
}
// A function pointer uses FuncPtr.null, and its pred is emp.
void call_fnptr(void) {
    _ghost_stmt(Pulse.Lib.C.Nullable.intro_unless_null_null (Pulse.Lib.C.FuncPtr.null (Int32.t & Int32.t) Int32.t) emp);
    takes_nullable_fnptr(NULL);
    _ghost_stmt(Pulse.Lib.C.Nullable.elim_unless_null_null (Pulse.Lib.C.FuncPtr.null (Int32.t & Int32.t) Int32.t) _);
}
