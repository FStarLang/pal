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
    maybe_write(p, b);
}

bool native_outputs(_plain void **p, _plain bool *flag, void *value, bool write)
  _requires(_inline_pulse(Pulse.Lib.C.Palow.Scalar.ptr_pts_to_uninit $(p)))
  _requires(_inline_pulse(Pulse.Lib.C.Palow.CTypes.bool_t_pts_to_uninit $(flag)))
  _ensures(_inline_pulse(
    if $(return) then
      ptr_pts_to $(p) 1.0R $(value) ** bool_t_pts_to $(flag) 1.0R $(write)
    else ptr_pts_to_uninit $(p) ** bool_t_pts_to_uninit $(flag)))
{
    if (!write) {
        return false;
    }
    *p = NULL;
    *p = value;
    *flag = true;
    return true;
}

void native_scalar(_plain uint32_t *p, uint32_t value)
  _requires(_inline_pulse(uint32_t_pts_to_uninit $(p)))
  _ensures(_inline_pulse(uint32_t_pts_to $(p) 1.0R $(value)))
{
    *p = value;
}

struct native_pair {
    uint32_t first;
    uint32_t second;
};

void native_fields(_plain struct native_pair *p, uint32_t value)
  _requires(_inline_pulse(Struct_native_pair.struct_native_pair_pts_to_uninit $(p)))
  _ensures(_inline_pulse(Struct_native_pair.struct_native_pair_pts_to $(p) 1.0R
    { Struct_native_pair.fld_first = 1ul; Struct_native_pair.fld_second = $(value) }))
{
    p->first = 1;
    p->second = value;
}
