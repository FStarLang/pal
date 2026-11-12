#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* An access through a walked pointer is focused out of the one array the
   pointer was walked through. Where that is not a single `_array`
   parameter, the access is refused rather than focused at a guess. */

int two_arrays(_array const int *a, _array const int *b, int c)
	_requires(a._length == 2 && b._length == 2)
{
	const int *p = c ? a : b;
	p++;
	return *p;
}

int not_from_an_array(_array const int *a, const int *q, int c)
	_requires(a._length == 2)
{
	const int *p = a;
	if (c) p = q;
	p++;
	return *p;
}

/* A narrowing conversion of a distance is not the distance: at 256,
   `(uint8_t)(p - a)` is 0. It is refused rather than read as the count. */
void narrowed_distance(_array const uint8_t *a, size_t n)
	_requires(a._length == n && n == 300)
{
	const uint8_t *p = a;
	size_t i = 0;
	while (i < 256)
		_invariant(i <= 256 && p - a == (_specint)i && (uint8_t)(p - a) == (_specint)i)
	{ p++; i++; }
}
