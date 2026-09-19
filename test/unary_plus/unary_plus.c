#include "pal.h"
#include <stdint.h>

int32_t plus_i32(int32_t x)
    _ensures(return == x)
{
    return +x;
}

uint32_t plus_u32(uint32_t x)
    _ensures(return == x)
{
    return +x;
}

int32_t plus_i8_promoted(int8_t x)
    _ensures(return == (int32_t)x)
{
    return +x;
}

int32_t plus_u8_promoted(uint8_t x)
    _ensures(return == (int32_t)x)
{
    return +x;
}

static int32_t increment_and_return_old(int32_t *p)
    _requires(*p == 5)
    _ensures(*p == 6)
    _ensures(return == 5)
{
    int32_t old = *p;
    *p = old + 1;
    return old;
}

int32_t plus_call(void)
    _ensures(return == 5)
{
    int32_t x = 5;
    int32_t old = +increment_and_return_old(&x);
    _assert(x == 6);
    return old;
}
