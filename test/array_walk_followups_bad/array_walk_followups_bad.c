#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* A write through a walked pointer at the other signedness of the element
   type is not supported; only reads convert. */
void clear(_array char *_d, size_t n)
	_requires(n <= _d._length)
{
	unsigned char *d = (void *)_d;
	for (; n; n--, d++)
		_invariant(d - _d + n == _old(n))
		*d = 0;
}

/* A callee whose contract may return a pointer into either argument: its
   result is not a pointer into any one array. */
char *either(_array const char *a, _array const char *b)
	_requires(a._length > 0 && b._length > 0)
	_ensures(return == a || return == b);

char read_either(_array const char *a, _array const char *b)
	_requires(a._length > 0 && b._length > 0)
{
	const char *p = either(a, b);
	return *p;
}
