#include "pal.h"
#include <stdint.h>

/* --- Arithmetic compound assignments --- */

int32_t test_add_assign(int32_t a, int32_t b)
    _requires(a < 1000 && b < 1000 && a > -1000 && b > -1000)
    _ensures(return == a + b)
{
    a += b;
    return a;
}

int32_t test_sub_assign(int32_t a, int32_t b)
    _requires(a < 1000 && b < 1000 && a > -1000 && b > -1000)
    _ensures(return == a - b)
{
    a -= b;
    return a;
}

int32_t test_mul_assign(int32_t a, int32_t b)
    _requires(a < 100 && b < 100 && a > -100 && b > -100)
    _ensures(return == a * b)
{
    a *= b;
    return a;
}

/* --- Bitwise compound assignments --- */

uint32_t test_and_assign(uint32_t a, uint32_t b)
    _ensures(return == (a & b))
{
    a &= b;
    return a;
}

uint32_t test_or_assign(uint32_t a, uint32_t b)
    _ensures(return == (a | b))
{
    a |= b;
    return a;
}

uint32_t test_xor_assign(uint32_t a, uint32_t b)
    _ensures(return == (a ^ b))
{
    a ^= b;
    return a;
}

/* --- Shift compound assignments --- */

uint32_t test_shl_assign(uint32_t a, uint32_t b)
    _requires(b < 32)
    _ensures(return == (a << b))
{
    a <<= b;
    return a;
}

uint32_t test_shr_assign(uint32_t a, uint32_t b)
    _requires(b < 32)
    _ensures(return == (a >> b))
{
    a >>= b;
    return a;
}

/* --- Chained compound assignments --- */

int32_t test_chain(int32_t x)
    _requires(x > 0 && x < 100)
    _ensures(return == x + x + x)
{
    int32_t a = x;
    a += x;
    a += x;
    return a;
}
