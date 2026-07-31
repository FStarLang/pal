#include "pal.h"
#include <stdint.h>
#include <stddef.h>

typedef int (*binary_fn)(int, int);

typedef union {
    int x;
    double y;
} int_or_double;

typedef struct {
    int values[0];
} zero_sized_struct;

typedef union {
    int values[0];
} zero_sized_union;

size_t size_of_int(void)
    _ensures(return > 0)
{
    return sizeof(int);
}

size_t size_of_bool_positive(void)
    _ensures(return > 0)
{
    return sizeof(_Bool);
}

size_t size_of_int8_positive(void)
    _ensures(return > 0)
{
    return sizeof(int8_t);
}

size_t size_of_uint8_positive(void)
    _ensures(return > 0)
{
    return sizeof(uint8_t);
}

size_t size_of_int16_positive(void)
    _ensures(return > 0)
{
    return sizeof(int16_t);
}

size_t size_of_uint16_positive(void)
    _ensures(return > 0)
{
    return sizeof(uint16_t);
}

size_t size_of_int32_positive(void)
    _ensures(return > 0)
{
    return sizeof(int32_t);
}

size_t size_of_uint32_positive(void)
    _ensures(return > 0)
{
    return sizeof(uint32_t);
}

size_t size_of_int64_positive(void)
    _ensures(return > 0)
{
    return sizeof(int64_t);
}

size_t size_of_uint64_positive(void)
    _ensures(return > 0)
{
    return sizeof(uint64_t);
}

size_t size_of_float_positive(void)
    _ensures(return > 0)
{
    return sizeof(float);
}

size_t size_of_double_positive(void)
    _ensures(return > 0)
{
    return sizeof(double);
}

size_t size_of_sizet_positive(void)
    _ensures(return > 0)
{
    return sizeof(size_t);
}

size_t size_of_ptrdifft_positive(void)
    _ensures(return > 0)
{
    return sizeof(ptrdiff_t);
}

size_t size_of_pointer_positive(void)
    _ensures(return > 0)
{
    return sizeof(int *);
}

size_t size_of_function_pointer_positive(void)
    _ensures(return > 0)
{
    return sizeof(binary_fn);
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

size_t size_of_two_ints_positive(void)
    _ensures(return > 0)
{
    return sizeof(two_ints);
}

size_t size_of_union_positive(void)
    _ensures(return > 0)
{
    return sizeof(int_or_double);
}

size_t size_of_zero_sized_struct(void)
    _ensures(return >= 0)
{
    return sizeof(zero_sized_struct);
}

size_t size_of_zero_sized_union(void)
    _ensures(return >= 0)
{
    return sizeof(zero_sized_union);
}

size_t align_of_int(void)
    _ensures(return > 0)
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
