// Tests: Increment, decrement, and compound assignment operators
//
// Compound assignments (+=, -=, *=, etc.) are tested in binary_ops.c.
// These operators are syntactic sugar for existing supported operations.
// pal desugars them during translation.

#include "pal.h"
#include <stdint.h>

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
