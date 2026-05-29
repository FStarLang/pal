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

size_t bytes_for_10_ints(void)
    _ensures(return == 10 * sizeof(int))
{
    return (size_t) 10 * sizeof(int);
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
    _ensures(return == 8 * sizeof(int))
{
    return sizeof(int[8]);
}

size_t align_of_int(void)
    _ensures(return == _Alignof(int))
{
    return _Alignof(int);
}
