// Test: Pointer equality between arbitrary pointers (not just NULL).

#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

bool ptrs_equal(_plain int32_t *a, _plain int32_t *b)
    _ensures(return == (a == b))
{
    return (a == b);
}

bool ptrs_not_equal(_plain int32_t *a, _plain int32_t *b)
    _ensures(return != (a == b))
{
    return (a != b);
}
