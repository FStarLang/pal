#include "pal.h"
#include <stdint.h>
#include <stdbool.h>

// clang-format off
bool multiply_u64(uint64_t a, uint64_t b, _out uint64_t *result)
    _ensures((_Bool)_inline_pulse(
        FStar.UInt64.v $(*result) ==
            (FStar.UInt64.v $(a) * FStar.UInt64.v $(b)) % pow2 64
        /\ ($(return) <==> FStar.UInt64.v $(a) * FStar.UInt64.v $(b) >= pow2 64)))
// clang-format on
{
    return __builtin_mul_overflow(a, b, result);
}

// clang-format off
bool multiply_unsigned_long(unsigned long a, unsigned long b, _out unsigned long *result)
    _ensures((_Bool)_inline_pulse(
        ($(return) \/ FStar.UInt64.v $(*result) == FStar.UInt64.v $(a) * FStar.UInt64.v $(b))
        /\ ($(return) <==> FStar.UInt64.v $(a) * FStar.UInt64.v $(b) >= pow2 64)))
// clang-format on
{
    return __builtin_mul_overflow(a, b, result);
}

void boundary_cases(void)
{
    uint64_t result;
    bool overflow = __builtin_mul_overflow(UINT64_MAX, UINT64_MAX, &result);
    _assert(overflow);
    overflow = __builtin_mul_overflow(4294967296u, 4294967296u, &result);
    _assert(overflow);
    overflow = __builtin_mul_overflow(UINT64_MAX, 1u, &result);
    _assert(!overflow && result == UINT64_MAX);
    overflow = __builtin_mul_overflow(4294967296u, 3u, &result);
    _assert(!overflow && result == 12884901888ul);
}
