#include "pal.h"
#include <stdint.h>

// Test: wrapping (modular) arithmetic for unsigned integers.
//
// In C, unsigned `+`, `-`, `*` are defined to wrap modulo 2^N. For uint32/uint64
// (which are not subject to integer promotion) PAL emits total wrapping
// operations whose result is exact when it fits and the modular value otherwise.
// None of the overflowing functions below would verify under a no-overflow
// precondition. uint8/uint16 wrap via promotion to int + narrowing cast.

/* --- uint32: overflow / underflow on + - * (uses the wrapping ops) --- */

uint32_t u32_add_overflow(uint32_t a)
    _requires(a == 4294967295)
    _ensures(return == 0)
{
    return a + 1;
}

uint32_t u32_sub_underflow(void)
    _ensures(return == UINT32_MAX)
{
    uint32_t x = 0;
    return x - 1;
}

uint32_t u32_mul_overflow(void)
    _ensures(return == 0)
{
    uint32_t x = 65536;
    return x * x;
}

uint32_t u32_mul_wrap_nonzero(void)
    _ensures(return == 65536)
{
    uint32_t x = 65536;
    return x * (x + 1);
}

/* --- uint64: overflow / underflow (uses the wrapping ops) --- */

uint64_t u64_sub_underflow(void)
    _ensures(return == UINT64_MAX)
{
    uint64_t x = 0;
    return x - 1;
}

uint64_t u64_mul_overflow(void)
    _ensures(return == 0)
{
    uint64_t x = 4294967296;
    return x * x;
}

/* --- uint8 / uint16: wrap via promotion + narrowing --- */

uint8_t u8_sub_underflow(void)
    _ensures(return == UINT8_MAX)
{
    uint8_t x = 0;
    return x - 1;
}

uint16_t u16_sub_underflow(void)
    _ensures(return == UINT16_MAX)
{
    uint16_t x = 0;
    return x - 1;
}

/* --- backward-compatible exact case (no overflow) --- */

uint32_t u32_add_exact(uint32_t a, uint32_t b)
    _requires(a <= 1000 && b <= 1000)
    _ensures(return == a + b)
{
    return a + b;
}
