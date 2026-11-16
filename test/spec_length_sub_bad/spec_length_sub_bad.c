#include <stddef.h>
#include "pal.h"

/* `s._length - 1` is the mathematical difference: a one-element array does
   not meet `1 <= s._length - 1`. */
int c1(_array const char *s) _requires(1 <= s._length - 1) _ensures(return == 0);

int use(_array const char *s)
	_requires(s._length >= 1)
	_ensures(return == 0)
{
	return c1(s);
}
