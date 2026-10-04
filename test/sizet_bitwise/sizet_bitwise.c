#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* C's bitwise operators apply to size_t like to any unsigned type. PAL models
 * size_t as exactly 64 bits (Pulse.Lib.C.Assumptions), so they translate to
 * Pulse.Lib.C.SizeTBits operators specified through FStar.UInt at width 64. */

size_t and_mask(size_t x) { return x & ~((size_t)4095); }

size_t or_bits(size_t x, size_t y) { return x | y; }

size_t xor_bits(size_t x, size_t y) { return x ^ y; }

size_t not_bits(size_t x) { return ~x; }

size_t shift_left_bits(size_t x) { return x << 3; }

size_t shift_right_bits(size_t x) { return x >> 12; }

/* The usual align-up idiom: round x up to a 4096-byte boundary. */
size_t align_up(size_t x)
    _requires(x < 4096)
{
    return ((x) + ((size_t)(1 << 12)) - 1) & ~(((size_t)(1 << 12)) - 1);
}

/* The postconditions are the FStar.UInt facts, so FStar.UInt lemmas apply. */
size_t and_le(size_t x, size_t m)
    _ensures(return <= x)
{
    _ghost_stmt(FStar.UInt.logand_le (Pulse.Lib.C.SizeTBits.v64 $(x)) (Pulse.Lib.C.SizeTBits.v64 $(m)));
    return x & m;
}

size_t compound_and(size_t x)
{
    x &= (size_t)7;
    x |= (size_t)8;
    x ^= (size_t)1;
    x <<= 1;
    x >>= 1;
    return x;
}
