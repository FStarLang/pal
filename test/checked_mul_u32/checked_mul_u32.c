#include "pal.h"
#include <stdint.h>
#include <stdbool.h>

// clang-format off
bool multiply_wide(uint64_t a, uint64_t b, _out uint32_t *result)
    _ensures((_Bool)_inline_pulse(
        FStar.UInt32.v $(*result) ==
            (FStar.UInt64.v $(a) * FStar.UInt64.v $(b)) % pow2 32
        /\ ($(return) <==> FStar.UInt64.v $(a) * FStar.UInt64.v $(b) >= pow2 32)))
// clang-format on
{
    return __builtin_mul_overflow(a, b, result);
}

// clang-format off
bool overwrite_pointer(uint64_t a, uint64_t b, uint32_t *result)
    _ensures((_Bool)_inline_pulse(
        FStar.UInt32.v $(*result) ==
            (FStar.UInt64.v $(a) * FStar.UInt64.v $(b)) % pow2 32
        /\ ($(return) <==> FStar.UInt64.v $(a) * FStar.UInt64.v $(b) >= pow2 32)))
// clang-format on
{
    return __builtin_mul_overflow(a, b, result);
}

void discarded_result(uint32_t *result)
    _ensures(*result == 42u)
{
    __builtin_mul_overflow(6u, 7u, result);
}

// clang-format off
uint32_t multiply_in_place(uint32_t a, uint64_t b)
    _ensures(_inline_pulse(pure(
        FStar.UInt32.v $(return) ==
            (FStar.UInt32.v $(a) * FStar.UInt64.v $(b)) % pow2 32)))
// clang-format on
{
    uint32_t result = a;
    bool overflow = __builtin_mul_overflow(result, b, &result);
    return result;
}

struct pair {
    uint32_t value;
    uint32_t other;
};

void write_field(struct pair *p)
    _ensures(p->value == 42 && p->other == _old(p->other))
{
    bool overflow = __builtin_mul_overflow(6u, 7u, &p->value);
    _assert(!overflow);
}

uint32_t conditional_write(bool write)
    _ensures(return == (write ? 42u : 17u))
{
    uint32_t result = 17u;
    // clang-format off
    if (write)
        _ensures(_inline_pulse(
            exists* value. Pulse.Lib.C.Palow.Scalar.uint32_t_pts_to $&(result) 1.0R value **
            pure (FStar.UInt32.v value == (if $(write) then 42 else 17))))
    {
        bool overflow = __builtin_mul_overflow(6u, 7u, &result);
        _assert(!overflow);
    }
    // clang-format on
    return result;
}

void boundary_cases(void)
{
    uint32_t result;
    bool overflow = __builtin_mul_overflow(UINT64_MAX, UINT64_MAX, &result);
    _assert(overflow && result == 1u);
    overflow = __builtin_mul_overflow(65536u, 65536u, &result);
    _assert(overflow && result == 0u);
    overflow = __builtin_mul_overflow(UINT32_MAX, 1u, &result);
    _assert(!overflow && result == UINT32_MAX);
    overflow = __builtin_mul_overflow(0u, UINT64_MAX, &result);
    _assert(!overflow && result == 0u);
}
