#include "pal.h"
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* C converts an integer to a narrower unsigned type by reducing it modulo the
 * target width, so a cast out of `size_t` is total: it never needs a proof that
 * the value fits. In particular it must work for `sizeof`, whose value PAL
 * keeps opaque, so nothing can be proven about how large it is. */

uint64_t sizeof_int_as_u64(void)
{
    return (uint64_t) sizeof(int);
}

uint32_t sizeof_int_as_u32(void)
{
    return (uint32_t) sizeof(int);
}

uint16_t sizeof_int_as_u16(void)
{
    return (uint16_t) sizeof(int);
}

uint8_t sizeof_int_as_u8(void)
{
    return (uint8_t) sizeof(int);
}

int64_t sizeof_int_as_i64(void)
{
    return (int64_t) sizeof(int);
}

int32_t sizeof_int_as_i32(void)
{
    return (int32_t) sizeof(int);
}

int16_t sizeof_int_as_i16(void)
{
    return (int16_t) sizeof(int);
}

int8_t sizeof_int_as_i8(void)
{
    return (int8_t) sizeof(int);
}

/* When the value does fit, the modular conversion still leaves it unchanged. */

uint32_t small_sizet_as_u32(size_t n)
    _requires((_specint) n < 4294967296)
    _ensures((_specint) return == (_specint) n)
{
    return (uint32_t) n;
}

uint64_t sizet_as_u64(size_t n)
    _requires((_specint) n < 18446744073709551616)
    _ensures((_specint) return == (_specint) n)
{
    return (uint64_t) n;
}

/* The reverse direction: every value of a `uint64_t` fits in `size_t`. */

size_t u64_as_sizet(uint64_t n)
    _ensures((_specint) return == (_specint) n)
{
    return (size_t) n;
}

/* Assertion conditions are C-preprocessed, so a `false` written here arrives at
 * PAL as the literal 0; C truthiness says it is the false proposition. */

void unreachable_assert(int32_t x)
    _requires(x != x)
{
    _assert(false);
}
