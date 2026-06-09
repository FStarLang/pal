// Tests: Increment, decrement, and compound assignment operators
//
// Compound assignments (+=, -=, *=, etc.) are tested in binary_ops.c.
// These operators are syntactic sugar for existing supported operations.
// pal desugars them during translation.

#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

uint32_t test_post_incr(uint32_t a)
    _requires(a < 1000)
{
    a++;
    return a;
}

uint32_t test_pre_incr(uint32_t a)
    _requires(a < 1000)
{
    ++a;
    return a;
}

uint32_t test_post_decr(uint32_t a)
    _requires(a > 0)
{
    a--;
    return a;
}

uint32_t test_pre_decr(uint32_t a)
    _requires(a > 0)
{
    --a;
    return a;
}

int test_incr_decr(int a)
    _requires(a < INT32_MAX - 1)
{
    a++;
    ++a;
    a--;
    --a;
    return a;
}

int test_compound_assign(int a)
    _requires(INT32_MIN <= (_specint) a * 2)
    _requires((_specint) a * 2 <= INT32_MAX)
{
    a += 1;
    a -= 1;
    a *= 2;
    a /= 1;
    return a;
}

size_t test_sizet_incr(size_t a)
    _requires((_specnat) a < UINT32_MAX)
{
    a++;
    a--;
    return a;
}

uint32_t test_u32_incr(uint32_t a)
    _requires(a < UINT32_MAX)
{
    a++;
    a--;
    return a;
}
