#include "pal.h"
#include <stdint.h>

/* Test: assignment as rvalue (x = (y = expr)) */
int32_t chain_assign(int32_t val)
    _requires(val > 0 && val < 100)
    _ensures(return == val)
{
    int32_t a;
    int32_t b;
    a = b = val;
    return a;
}

/* Test: compound assignment as rvalue */
int32_t compound_assign_rvalue(int32_t x)
    _requires(x > 0 && x < 50)
    _ensures(return == x + x)
{
    int32_t y = x;
    int32_t z = (y += x);
    return z;
}
