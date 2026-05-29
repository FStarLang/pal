#include "pal.h"
#include <stdint.h>
#include <stddef.h>

// sizeof of a builtin type in a size_t-position
size_t size_of_int(void)
{
    return sizeof(int);
}

// sizeof of an expression (clang folds based on the expression's type)
size_t size_of_expr(int x)
{
    return sizeof(x);
}

// sizeof participating in arithmetic against another size_t literal
size_t bytes_for_10_ints(void)
{
    return (size_t) 10 * sizeof(int);
}

// sizeof of a struct type
typedef struct {
    int x;
    int y;
} two_ints;

size_t size_of_two_ints(void)
{
    return sizeof(two_ints);
}

// sizeof of an array type
size_t size_of_int_array(void)
{
    return sizeof(int[8]);
}

// Cast sizeof to a narrower integer type (exercises the new SizeT -> Int cast).
uint32_t size_of_int_u32(void)
{
    return (uint32_t) sizeof(int);
}

// _Alignof of a builtin type
size_t align_of_int(void)
{
    return _Alignof(int);
}

