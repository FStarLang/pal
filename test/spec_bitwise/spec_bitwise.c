#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* musl's strspn/strcspn keep a 256-bit set of bytes in four words. */
#define BITOP(a,b,op) \
 ((a)[(size_t)(b)/64] op (uint64_t)1<<((size_t)(b)%64))

/* A contract reads a bit as `(w >> k) & 1`. The shift amount must be below
   the width, which is a well-formedness guard of the clause. */
int member(_array const uint64_t *set, unsigned char b)
	_requires(set._length == 4)
	_ensures((return != 0) == (((set[b / 64] >> (b % 64)) & 1) != 0))
{
	return ((set[(size_t)b / 64] >> ((size_t)b % 64)) & 1) != 0;
}

/* Setting a bit with musl's BITOP makes the contract's bit read true. */
void add(_array uint64_t *set, unsigned char b)
	_requires(set._length == 4)
	_ensures(set._length == 4)
	_ensures(((set[b / 64] >> (b % 64)) & 1) != 0)
{
	BITOP(set, b, |=);
}

/* strspn's first loop: put every byte of `c` into the set. */
void build(_array uint64_t *set, _array const unsigned char *c)
	_requires(set._length == 4)
	_requires(_exists(size_t i, i < c._length && c[i] == 0))
	_ensures(set._length == 4)
{
	for (; *c; c++)
		_invariant(set._length == 4)
		_invariant(_exists(size_t i, c - _old(c) <= i && i < _old(c)._length && _old(c)[i] == 0))
		BITOP(set, *c, |=);
}

/* Every bitwise operator, on `size_t` and on a narrower unsigned type. */
void ops(size_t x, uint32_t y)
	_requires((x & 1) == 1 && (x | 2) == x && (x ^ x) == 0 && (~x & x) == 0)
	_requires((x << 1) >> 1 == (x & ~((size_t)1 << 63)))
	_requires((y >> 31) <= 1)
	_ensures((x & 1) == 1 && (y >> 31) <= 1)
{
}
