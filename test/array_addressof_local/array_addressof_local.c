#include "pal.h"
#include <stdint.h>
#include <stddef.h>

// `&a[i]` over a real `_array` whose result is used as a plain `int *`
// (a Pulse `ref`) is *not* desugared to `a + i`; instead PAL borrows exactly
// cell `i` with `array_borrow_cell`. The borrow is effectful, so it is hoisted
// into a preceding statement and the binding is reused wherever `&a[i]`
// appeared. The matching `array_return_cell` is invoked manually via inline
// Pulse. These tests cover the general (non-call-argument) contexts.

// A helper taking a plain `int *` (a Pulse `ref`), to exercise a borrowed
// cell stored in a local being forwarded to a call argument.
void store7(int *p)
  _ensures(*p == 7)
{
    *p = 7;
}

// Pattern 1: bind `&a[i]` to a local `int *` and write through it.
void write_via_local(_array int *a, size_t i)
  _requires(i < a._length)
{
    int *p = &a[i];
    *p = 7;
    _ghost_stmt(array_return_cell $(a) $(i));
}

// Pattern 2: bind `&a[i]` to a local and read through it (then write the
// value back so the cell stays initialized).
void read_via_local(_array int *a, size_t i)
  _requires(i < a._length)
{
    int *p = &a[i];
    int x = *p;
    *p = x;
    _ghost_stmt(array_return_cell $(a) $(i));
}

// Pattern 3: constant index.
void const_index(_array int *a)
  _requires(a._length > 0)
{
    int *p = &a[0];
    *p = 3;
    _ghost_stmt(array_return_cell $(a) 0sz);
}

// Pattern 4: the borrowed local is forwarded to a function expecting `int *`.
void forward_to_call(_array int *a, size_t i)
  _requires(i < a._length)
{
    int *p = &a[i];
    store7(p);
    _ghost_stmt(array_return_cell $(a) $(i));
}

// Pattern 5: index held in a `size_t` variable (a non-literal index where the
// borrow and the manual return use the same value).
void var_index(_array int *a, size_t i)
  _requires(i < a._length)
{
    size_t j = i;
    int *p = &a[j];
    *p = 5;
    _ghost_stmt(array_return_cell $(a) $(j));
}

// Pattern 6: the *other* lowering path. Here `&a[i]` is returned as an
// `_arrayptr`, so it is NOT borrowed but desugared to `a + i`
// (`array_to_arrayptr`). The caller below then receives that arrayptr into a
// *plain* `int *`, so PAL refines the declared `ref` to an `arrayptr` (from the
// call's return type) and `*p` lowers to `arrayptr_read`.
//
// For the caller to dereference the pointer it gets back, the getter must
// export not just the `arrayptr_pts_to` permission but also the returned
// pointer's *offset*: `arrayptr_pts_to return a` only pins `base_of`/`length`,
// and without `offset_of return` the caller cannot prove the cell it reads is
// in bounds and initialized (`arrayptr_read` needs
// `array_spec_initd s (arrayptr_off return a + 0)`). `$(i)` antiquotes to a
// `SizeT.t`, so it is wrapped in `SizeT.v` to match `offset_of`'s `int`.
_arrayptr int *nth_ptr(_array int *a, size_t i)
  _preserves(i < a._length)
  _ensures(_inline_pulse(arrayptr_pts_to $(return) $(a)
    ** pure (offset_of $(return) == offset_of $(a) + SizeT.v $(i))))
{
    return &a[i];
}

// Pattern 7: receive the returned arrayptr into a plain `int *` and read it.
int read_via_returned_ptr(_array int *a, size_t i)
  _requires(i < a._length)
{
    int *p = nth_ptr(a, i);
    return *p;
}
