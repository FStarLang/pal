// An `_assert` over a call whose contract determines its result is read as
// the term the contract names, so it is proved, not assumed: each assertion
// below is false for every argument the caller's precondition allows, and
// expected-verification-failures.txt requires each caller to be rejected. The
// callees have real bodies, which do verify.

#include "pal.h"

#include <stdint.h>

_Bool
is_small(uint32_t x)
    _ensures(return == (_Bool)_inline_pulse(UInt32.v $(x) < 10))
{
    return x < 10u;
}

uint32_t
low_bit(uint32_t x)
    _ensures(return == (uint32_t)_inline_pulse(UInt32.logand $(x) 1ul))
{
    return x & 1u;
}

void
small_is_not_small(uint32_t x)
    _requires(x < 5u)
{
    _assert(!is_small(x));
}

void
odd_low_bit_is_zero(uint32_t x)
    _requires(x == 3u)
{
    _assert(low_bit(x) == 0);
}
