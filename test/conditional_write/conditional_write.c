#include "pal.h"
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

// Takes an uninitialized `int *` out-parameter and initializes it on every
// path: 42 when `b` is true, 0 otherwise. Because the cell is always written,
// this is a plain `_out` function (uninitialized `ref` in, initialized `ref`
// out) and needs no hand-written ownership spec at all.
void maybe_write(_out int *p, bool b)
{
    if (b) {
        *p = 42;
    } else {
        *p = 0;
    }
}

// Borrow cell 0 of an uninitialized length-1 array, hand it to `maybe_write`,
// then give the cell back, leaving the array fully initialized. `_out _array`
// requires `a` uninitialized on entry and fully initialized on exit (so no
// hand-written array spec is needed). `maybe_write` is a plain `_out` function,
// so it wants an uninitialized `ref` (`pts_to_uninit`). PAL borrows the cell as
// a maybe-cell without guessing its state, so we borrow it into a local `ref`
// (`int *p = &a[0]`) and drop its value with `forget_maybe` by hand to obtain
// that uninitialized `ref`. Once `maybe_write` initializes the cell, we package
// it back as a maybe-cell (`intro_maybe_some`) and return it with the single
// `array_return_cell`.
void caller(_out _array int *a, bool b)
  _requires(a._length == 1)
{
    int *p = &a[0];
    _ghost_stmt(Pulse.Lib.C.MaybeUninit.forget_maybe $(p));
    maybe_write(p, b);
    _ghost_stmt(Pulse.Lib.C.MaybeUninit.intro_maybe_some (array_cell_ref $(a) (SizeT.v 0sz)));
    _ghost_stmt(array_return_cell $(a));
}
