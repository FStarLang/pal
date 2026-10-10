// Subscripting a published global array of structs (#358).
#include "pal.h"
#include <stdint.h>
#include <stddef.h>

struct desc {
	int offset;
};

static const struct desc table[2] = {
	{ .offset = 0 },
	{ .offset = 8 },
};

_requires(j >= 0 && j < 2)
_ensures(return == 0 || return == 8)
int read_entry(int j)
{
	return table[j].offset;
}

struct inner {
	uint32_t lo, hi;
};

struct entry {
	struct inner range;
	uint8_t tag[2];
};

static const struct entry entries[3] = {
	{ .range = { .lo = 1, .hi = 2 }, .tag = { 7, 8 } },
	{ .range = { .lo = 3, .hi = 4 }, .tag = { 9, 10 } },
	{ .range = { .lo = 5, .hi = 6 } },
};

_requires(i < 3)
_ensures(return == entries[i].range.hi - entries[i].range.lo)
uint32_t width(uint32_t i)
{
	return entries[i].range.hi - entries[i].range.lo;
}

_requires(i < 3 && k < 2)
uint8_t tag_of(size_t i, size_t k)
{
	return entries[i].tag[k];
}

uint32_t sum_lo(void)
{
	uint32_t s = 0;
	for (size_t i = 0; i < 3; i++)
		_invariant(_live(i) && _live(s) && i <= 3)
	{
		s += entries[i].range.lo;
	}
	return s;
}

static const int scalars[3] = { 4, 5, 6 };

_requires(i < 3)
_ensures(return == scalars[i])
int scalar_at(uint32_t i)
{
	return scalars[i];
}
