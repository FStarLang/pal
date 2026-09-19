#include <stddef.h>
#include <stdint.h>

#include "pal.h"

/*
 * A large `= {0}` initializer.
 *
 * The point of this test is the *length* of the resulting spec. Translated as
 * a list of Cons cells, `array_spec_len` of the initializer does not reach the
 * solver at all -- the typing axiom for `array_spec_of_list_with_len` is
 * guarded on an erased proof implicit -- so `n <= array_spec_len (...)` is
 * unprovable from about 32 elements up, and any use of such a buffer as an
 * `_array` argument fails. `emit.rs` therefore emits `array_spec_const` when
 * every element denotes the same value, and this file checks that both the
 * length and the fullness of the result are available.
 *
 * Note that the elements of `= {0}` are not syntactically equal: the `0` the
 * programmer wrote arrives as a cast of an `int` literal while the zeros clang
 * pads with are bare `int8` literals. Sizes on both sides of the old
 * 16-element threshold are exercised.
 */

void sink(_array uint8_t *buf, size_t n) _requires(buf._length >= n)
	_preserves_value(buf._length);

void small_zero(void)
{
	uint8_t buf[8] = { 0 };

	sink(buf, sizeof(buf));
}

void large_zero(void)
{
	uint8_t buf[64] = { 0 };

	sink(buf, sizeof(buf));
}

void very_large_zero(void)
{
	uint8_t buf[256] = { 0 };

	sink(buf, sizeof(buf));
}

/* Every element the same non-zero literal, written out. */
void uniform_nonzero(void)
{
	uint8_t buf[4] = { 7, 7, 7, 7 };

	sink(buf, sizeof(buf));
}

/*
 * Elements that differ. This must still take the list path and still be
 * correct; below sixteen elements the list path works.
 */
uint8_t mixed(void)
{
	uint8_t buf[4] = { 1, 2, 3, 4 };

	return buf[2];
}
