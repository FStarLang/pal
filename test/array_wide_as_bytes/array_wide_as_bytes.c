/* Only `char` arrays have a byte view so far; wider elements are refused. */
#include "pal.h"
#include <stddef.h>

void *my_memset(_array void *dest, int c, size_t n)
	_requires(n <= dest._length);

void clear(_array int *a, size_t n)
	_requires(n <= a._length)
{
	my_memset(a, 0, n);
}
