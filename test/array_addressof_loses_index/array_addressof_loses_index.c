#include "pal.h"
#include <stdint.h>

// These tests cover the case where `&a[i]` IS desugared to pointer
// arithmetic `a + i`. That happens when the address-of-element is used where
// an `_arrayptr` is expected: a single-cell `ref` borrow could not represent
// the resulting slice, so PAL keeps the index by emitting `array_to_arrayptr`
// (the `BinOp::Add` / arrayptr path) instead of `array_borrow_cell`. Contrast
// with test/array_addressof_local, where the same `&a[i]` over a real
// `_array` flows into a plain `int *` and so borrows a single cell.

// `&a[3]` returned as an `_arrayptr` lowers to `array_to_arrayptr a 3`, an
// aliasing view that retains offset 3 without consuming the array.
_arrayptr int* via_addressof_const(_array int* a)
{
    return &a[3];
}

typedef struct containercopy {
    _array int* Elements;
} containercopy;

// Same arithmetic lowering through a struct field: `&c->Elements[3]`.
_arrayptr int* get_via_addressof_const(containercopy* c)
{
    return &c->Elements[3];
}
