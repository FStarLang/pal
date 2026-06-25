#include "pal.h"
#include <stdint.h>
#include <stddef.h>

// `write_to` takes a plain `int *` (Pulse `ref`) and writes through it.
void write_to(int *p)
  _ensures(*p == 42)
{
    *p = 42;
}

// `caller` holds a real `_array int *` and passes the address of element `i`
// to `write_to`. PAL borrows a `ref` from the array cell at `i` (forward
// direction, emitted automatically). The borrowed cell is returned to the
// array manually via inline Pulse (backward direction).
void caller(_array int *a, size_t i)
  _requires(i < a._length)
{
    write_to(&a[i]);
    _ghost_stmt(array_return_cell $(a) $(i));
}

// `init_cell` takes an `_out int *` — an *uninitialized* `ref`
// (`pts_to_uninit`) that it initializes by writing through.
void init_cell(_out int *p)
  _ensures(*p == 42)
{
    *p = 42;
}

// Passing `&a[i]` into an `_out` parameter borrows the cell as an
// *uninitialized* `ref` (PAL emits `array_borrow_cell_uninit`, which forgets
// the cell's value). Once `init_cell` writes through it, the cell is returned
// (now initialized) with the same manual `array_return_cell`.
void caller_out(_array int *a, size_t i)
  _requires(i < a._length)
{
    init_cell(&a[i]);
    _ghost_stmt(array_return_cell $(a) $(i));
}

// Borrow a *genuinely uninitialized* array cell and write through it.
// `_out _array int *a` means PAL requires `a` uninitialized on entry and fully
// initialized on exit. With length 1, the cell at index 0 starts uninitialized;
// passing `&a[0]` to the `_out` parameter `init_cell` borrows it with
// `array_borrow_cell_uninit`, `init_cell` writes 42 through it, and returning
// the cell leaves the (length-1) array fully initialized.
void fill_first(_out _array int *a)
  _requires(a._length == 1)
{
    init_cell(&a[0]);
    _ghost_stmt(array_return_cell $(a) 0sz);
}

