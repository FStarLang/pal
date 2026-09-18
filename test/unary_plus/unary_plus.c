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
