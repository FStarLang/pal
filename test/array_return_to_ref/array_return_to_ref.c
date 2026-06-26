#include "pal.h"
#include <stdint.h>
#include <stddef.h>

// A function that returns an array pointer (`_arrayptr`), whose result is then
// received into a *plain* `int *` (a Pulse `ref`) at the call site:
//
//     int *myptr = first_ptr(a);
//
// PAL infers the pointer kind of `myptr` from the call's return type
// (`refine_decl_pointer_kind` in src/pass/elab.rs), so the declared `ref` is
// refined to an `arrayptr` and `*myptr` lowers to `arrayptr_read`/`write`.
//
// PAL's default auto-generated arrayptr-return spec only preserves the array's
// `array_pts_to` and *drops* the result's permission (see
// test/array_addressof_loses_index, whose returns are never dereferenced by a
// caller). To let the caller actually use the pointer it receives, this `F`
// explicitly exports, in its postcondition:
//   * `arrayptr_pts_to return a`        — the permission to use the arrayptr;
//   * `offset_of return == offset_of a` — pins the arrayptr at cell 0 of `a`;
//   * `a._length > 0`                   — so the caller knows cell 0 is in
//                                         bounds (masked/initialized) for the
//                                         new spec witness produced by the call.
_arrayptr int* first_ptr(_array int* a)
  _requires(a._length > 0)
  _ensures(a._length > 0)
  _ensures(_inline_pulse(arrayptr_pts_to $(return) $(a)
    ** pure (offset_of $(return) == offset_of $(a))))
{
    return &a[0];
}

// Pattern 1: receive the arrayptr in a plain `int *` and write through it.
void write_via_returned_ptr(_array int* a)
  _requires(a._length > 0)
{
    int* myptr = first_ptr(a);
    *myptr = 9;
    _ghost_stmt(arrayptr_drop $(myptr));
}

// Pattern 2: receive the arrayptr in a plain `int *` and read through it.
int read_via_returned_ptr(_array int* a)
  _requires(a._length > 0)
{
    int* myptr = first_ptr(a);
    int v = *myptr;
    _ghost_stmt(arrayptr_drop $(myptr));
    return v;
}
