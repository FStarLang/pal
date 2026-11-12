#include "pal.h"
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
