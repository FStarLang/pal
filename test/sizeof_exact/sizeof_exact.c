#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/*
 * The exact sizes of the fixed-width integer types, and the obligations that
 * need them.
 *
 * `Pulse.Lib.C.Sizeof` used to say only `sizeof(T) > 0` for every integer type
 * wider than a byte.  That is all C guarantees in the abstract, but it is less
 * than PAL's model already assumes: PAL maps a C integer type to
 * `FStar.UIntN.t` by its bit WIDTH and then gives it full N-bit modular
 * arithmetic over all N bits, which is to say a representation with no padding.
 * With no padding and CHAR_BIT == 8 -- which PAL also already assumes, by
 * mapping `char` to `FStar.UInt8.t` -- `sizeof(T)` is exactly N/8.  The
 * derivation is written out in full in Pulse.Lib.C.Sizeof.fsti.
 *
 * The practical consequence is this file.  `sizeof` almost never appears alone
 * in C; it appears multiplied or divided, and with only `sizeof > 0` known the
 * arithmetic cannot be shown to stay inside `size_t`, so an ordinary bounds
 * check fails on an obligation that has nothing to do with bounds.  The
 * motivating case was coco's `SET_ATTR_WITH_SIZE`, whose bound is
 *
 *     (sizeof(attr_group) * 8) / attr_size
 *
 * and which failed with
 *
 *     Failed to prove: FStar.SizeT.fits
 *       (FStar.SizeT.v (c_sizeof (full_array_lspec FStar.UInt64.t 1)) * 8)
 *
 * -- the multiplication, not the comparison.
 *
 * Note the shapes used below.  `sizeof(<expression>)` is rejected inside an
 * annotation (coco/PAL_LIMITATIONS.md L43), so every bound here is an ordinary
 * C guard and every `_ensures` names a literal.  `sizeof(<type>[n])` does not
 * translate either, so array sizes are taken through a member.
 */

/* ------------------------------------------------------------------ *
 * 1. The bitmap idiom: how many entries fit, at k bits each.
 *
 * This is coco's SET_ATTR_WITH_SIZE reduced to its arithmetic.  Three separate
 * obligations need the exact size:
 *
 *   - `sizeof(a->bmap) * 8` must fit in size_t -- this is the one that failed;
 *   - the index `(id * 2) / 64` must be < 1, the array's length, which needs
 *     `sizeof(a->bmap) == 8` and not merely "positive";
 *   - the shift count `(id * 2) % 64` must be < 64, which is free.
 * ------------------------------------------------------------------ */

struct attrs {
	uint64_t bmap[1];		/* 64 bits -> 32 entries at 2 bits */
};

void set_attr(struct attrs *a, uint32_t id, uint64_t val)
{
	if (id >= (uint32_t)((sizeof(a->bmap) * 8) / 2))
		return;
	a->bmap[(id * 2) / 64] |= (val << ((id * 2) % 64));
}

/* ------------------------------------------------------------------ *
 * 2. Byte counts of typed buffers, as values a caller can be told.
 *
 * Before, each of these was "some positive multiple of the element count", so
 * the `_ensures` could not be proved.
 * ------------------------------------------------------------------ */

struct packet {
	uint16_t seq[4];
	uint32_t crc[2];
	uint64_t ts[8];
};

size_t seq_bytes(struct packet *p) _ensures(return == 8)  { return sizeof(p->seq); }
size_t crc_bytes(struct packet *p) _ensures(return == 8)  { return sizeof(p->crc); }
size_t ts_bytes(struct packet *p)  _ensures(return == 64) { return sizeof(p->ts); }

/* ------------------------------------------------------------------ *
 * 3. The types themselves, signed and unsigned, at every width PAL maps.
 * ------------------------------------------------------------------ */

size_t sz_i16(void) _ensures(return == 2) { return sizeof(int16_t); }
size_t sz_u16(void) _ensures(return == 2) { return sizeof(uint16_t); }
size_t sz_i32(void) _ensures(return == 4) { return sizeof(int32_t); }
size_t sz_u32(void) _ensures(return == 4) { return sizeof(uint32_t); }
size_t sz_i64(void) _ensures(return == 8) { return sizeof(int64_t); }
size_t sz_u64(void) _ensures(return == 8) { return sizeof(uint64_t); }

/* The byte types were already exact; here so the family is tested together. */
size_t sz_i8(void) _ensures(return == 1) { return sizeof(int8_t); }
size_t sz_u8(void) _ensures(return == 1) { return sizeof(uint8_t); }

/* ------------------------------------------------------------------ *
 * 4. ARRAY_SIZE still works.
 *
 * `sizeof(x) / sizeof(*(x))` reduces to the nonlinear `(s * n) / s == n` with
 * `s` uninterpreted -- see test/array_size_idiom, which checks that shape on
 * purpose, including for element types whose size is still uninterpreted.
 * With `s` concrete the goal becomes ordinary arithmetic, so this is here to
 * confirm the exact sizes did not disturb the idiom, not to test it.
 * ------------------------------------------------------------------ */

#define ARRAY_SIZE(x) (sizeof(x) / sizeof(*(x)))

uint64_t sum_ts(struct packet *p)
{
	uint32_t i = 0;
	uint64_t acc = 0;

	while (i < ARRAY_SIZE(p->ts))
		_invariant(_live(i))
		_invariant(_live(acc))
	{
		acc += p->ts[i];
		i++;
	}
	return acc;
}
