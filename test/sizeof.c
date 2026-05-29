#include "pal.h"
#include <stdint.h>
#include <stddef.h>

size_t size_of_int(void)
    _ensures(return == 4uz)
{
    return sizeof(int);
}

size_t size_of_expr(int x)
    _ensures(return == 4uz)
{
    return sizeof(x);
}

size_t bytes_for_10_ints(void)
    _ensures(return == 40uz)
{
    return (size_t) 10 * sizeof(int);
}

typedef struct {
    int x;
    int y;
} two_ints;

size_t size_of_two_ints(void)
    _ensures(return == 8uz)
{
    return sizeof(two_ints);
}

size_t size_of_int_array(void)
    _ensures(return == 32uz)
{
    return sizeof(int[8]);
}

uint32_t size_of_int_u32(void)
    _ensures(return == 4u)
{
    return (uint32_t) sizeof(int);
}

size_t align_of_int(void)
    _ensures(return == 4uz)
{
    return _Alignof(int);
}

