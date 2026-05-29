#include "pal.h"
#include <stdint.h>

uint32_t test_bitand(uint32_t a, uint32_t b)
    _ensures(return == (a & b))
{
    return a & b;
}

uint32_t test_bitor(uint32_t a, uint32_t b)
    _ensures(return == (a | b))
{
    return a | b;
}

uint32_t test_bitxor(uint32_t a, uint32_t b)
    _ensures(return == (a ^ b))
{
    return a ^ b;
}

uint32_t test_bitnot(uint32_t a)
    _ensures(return == ~a)
{
    return ~a;
}

uint32_t test_shl(uint32_t a, uint32_t b)
    _requires(b < 32u)
{
    return a << b;
}

uint32_t test_shr(uint32_t a, uint32_t b)
    _requires(b < 32u)
{
    return a >> b;
}

uint64_t test_shl64(uint64_t a, uint32_t b)
    _requires(b < 64u)
{
    return a << b;
}

uint64_t test_shr64(uint64_t a, uint32_t b)
    _requires(b < 64u)
{
    return a >> b;
}
