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
