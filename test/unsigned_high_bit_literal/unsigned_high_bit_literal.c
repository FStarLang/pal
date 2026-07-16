#include "pal.h"
#include <stdint.h>

/*
 * Regression test: 32-bit unsigned constants with the high bit set.
 *
 * The bug is value-based, not spelling-based: any uint32 literal in
 * [2^31, 2^32) (high bit set) triggers it, whether written in decimal or
 * hex. The width-32 fast path in Emitter::emit_rvalue printed the raw
 * (signed) literal value with a `ul` suffix, so clang's bit pattern for
 * 4294967295 (read as the signed BigInt -1) was emitted as `-1ul` and
 * 2147483648 as `-2147483648ul`. F* rejects both: unary `-` is integer
 * negation and does not apply to UInt32.t. The value must instead be
 * normalized into [0, 2^32) before printing (e.g. `4294967295ul`,
 * `2147483648ul`).
 *
 * Introduced by commit fbe8b95d ("Add global array with tactics example.").
 */

uint32_t uint32_max(void)
{
    return 4294967295u;
}

uint32_t uint32_high_bit(void)
{
    return 2147483648u;
}
