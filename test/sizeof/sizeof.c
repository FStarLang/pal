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

// Array sizeof related to element size. PAL takes every size straight from
// clang, so `sizeof(int[8])` translates to the literal `32sz`.
size_t size_of_int_array_len(void)
    _ensures(return == sizeof(int) * 8)
{
    return sizeof(int[8]);
}

// Zero-length array has size 0 (a GNU extension clang accepts).
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

// Sizes come from clang's target ABI rather than an opaque F* function, so
// exact values are provable. These are LP64 values; on a target with a
// different ABI clang would report different numbers and the postconditions
// would be adjusted with them.
size_t size_of_int_exact(void)
    _ensures(return == 4)
{
    return sizeof(int);
}

size_t size_of_two_ints_exact(void)
    _ensures(return == 8)
{
    return sizeof(two_ints);
}

size_t align_of_two_ints_exact(void)
    _ensures(return == 4)
{
    return _Alignof(two_ints);
}

// A struct with internal padding: `char` then `int` occupies 8 bytes, not 5.
typedef struct {
    char c;
    int i;
} padded;

size_t size_of_padded_exact(void)
    _ensures(return == 8)
{
    return sizeof(padded);
}
