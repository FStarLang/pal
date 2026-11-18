#include "pal.h"
#include <stddef.h>
#include <stdint.h>

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
