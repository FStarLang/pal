#include "pal.h"
#include <stdint.h>
#include <stddef.h>

size_t size_of_int(void)
    _ensures(return == sizeof(int))
{
    return sizeof(int);
}

size_t size_of_expr(int x)
    _ensures(return == sizeof(int))
{
    return sizeof(x);
}

typedef struct {
    int x;
    int y;
} two_ints;

size_t size_of_two_ints(void)
    _ensures(return == sizeof(two_ints))
{
    return sizeof(two_ints);
}

size_t size_of_int_array(void)
    _ensures(return == sizeof(int[8]))
{
    return sizeof(int[8]);
}

size_t align_of_int(void)
    _ensures(return == _Alignof(int))
{
    return _Alignof(int);
}

// Array sizeof related to element size. PAL translates `sizeof(int[8])` to
// `c_sizeof (full_array_lspec int 8)`, and the `c_sizeof_array` axiom relates
// it to `sizeof(int) * 8`.
size_t size_of_int_array_len(void)
    _ensures(return == sizeof(int) * 8)
{
    return sizeof(int[8]);
}

// Zero-length array has size 0: `c_sizeof (full_array_lspec int 0)` reduces to
// `sizeof(int) * 0 == 0` via the `c_sizeof_array` axiom.
size_t size_of_int_array_zero(void)
    _ensures(return == 0)
{
    return sizeof(int[0]);
}

#define ALIGN_OF(TypeOrExpression) _Alignof(__typeof__(TypeOrExpression))

size_t align_of_typeof_type(void)
    _ensures(return == _Alignof(two_ints))
{
    return ALIGN_OF(two_ints);
}

size_t align_of_typeof_expr(two_ints value)
    _ensures(return == _Alignof(two_ints))
{
    return ALIGN_OF(value);
}
