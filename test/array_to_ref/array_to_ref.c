#include "pal.h"
#include <stdint.h>
#include <stddef.h>

// `write_to` takes a plain `int *` (Pulse `ref`) and writes through it.
void write_to(int *p)
  _ensures(*p == 42)
{
    *p = 42;
}

// `caller` holds a real `_array int *` and wants to hand element `i` to
// `write_to`. Borrowing a cell out of an array always yields a
// `pts_to_maybe_uninit` cell carrying its current optional value; PAL does not
// guess whether that cell is initialized or not, so the adaptation to
// `write_to`'s readable `int *` is applied *by hand*. We borrow the cell into a
// local `ref` (`int *p = &a[i]` emits `array_borrow_cell`), then — since the
// array is fully initialized — reveal the known-initialized cell into a readable
// `pts_to` with `array_cell_read` before the call. To hand it back, we package
// the written cell as a maybe-cell (`intro_maybe_some`) and return it with
// `array_return_cell`.
void caller(_array int *a, size_t i)
  _requires(i < a._length)
{
    int *p = &a[i];
    _ghost_stmt(array_cell_read $(a) $(i));
    write_to(p);
    _ghost_stmt(Pulse.Lib.C.MaybeUninit.intro_maybe_some (array_cell_ref $(a) (SizeT.v $(i))));
    _ghost_stmt(array_return_cell $(a));
}

// `init_cell` takes an `_out int *` — an *uninitialized* `ref`
// (`pts_to_uninit`) that it initializes by writing through.
void init_cell(_out int *p)
  _ensures(*p == 42)
{
    *p = 42;
}

// Handing an array cell to an `_out` parameter. Again PAL only borrows the cell
// as a `pts_to_maybe_uninit`; the user drops its value with `forget_maybe` to
// obtain the uninitialized `ref` (`pts_to_uninit`) that `init_cell` expects.
// Once `init_cell` writes through it, the now-initialized cell is packaged back
// as a maybe-cell (`intro_maybe_some`) and returned with `array_return_cell`.
void caller_out(_array int *a, size_t i)
  _requires(i < a._length)
{
    int *p = &a[i];
    _ghost_stmt(Pulse.Lib.C.MaybeUninit.forget_maybe $(p));
    init_cell(p);
    _ghost_stmt(Pulse.Lib.C.MaybeUninit.intro_maybe_some (array_cell_ref $(a) (SizeT.v $(i))));
    _ghost_stmt(array_return_cell $(a));
}

// Borrow a *genuinely uninitialized* array cell and write through it.
// `_out _array int *a` means PAL requires `a` uninitialized on entry and fully
// initialized on exit. With length 1, the cell at index 0 starts uninitialized;
// borrowing `&a[0]` into a local `ref` hands it out as a maybe-cell, we drop its
// (absent) value with `forget_maybe`, `init_cell` writes 42 through it, and
// returning the cell (packaged as a maybe-cell) leaves the (length-1) array
// fully initialized.
void fill_first(_out _array int *a)
  _requires(a._length == 1)
{
    int *p = &a[0];
    _ghost_stmt(Pulse.Lib.C.MaybeUninit.forget_maybe $(p));
    init_cell(p);
    _ghost_stmt(Pulse.Lib.C.MaybeUninit.intro_maybe_some (array_cell_ref $(a) (SizeT.v 0sz)));
    _ghost_stmt(array_return_cell $(a));
}

