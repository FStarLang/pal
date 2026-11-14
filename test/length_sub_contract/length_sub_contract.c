#include <stddef.h>
#include "pal.h"

/* `_length` is a `_specint`, so subtracting from it in a contract is
   mathematical subtraction, with or without an explicit cast. */

int c1(_array const char *s) _requires(1 <= s._length - 1) _ensures(return == 0);
int c2(_array const char *s, size_t m)
	_requires(_exists(size_t k, k < s._length && 1 <= s._length - k)) _ensures(return == 0);
int c3(_array const char *s, size_t m)
	_requires(m < s._length && 1 <= (_specint)s._length - m) _ensures(return == 0);

int c1(const char *s) { return 0; }
int c2(const char *s, size_t m) { return 0; }
int c3(const char *s, size_t m) { return 0; }

char last(_array const char *s, size_t j)
	_requires(j < s._length - 1)
	_ensures(return == s[j + 1])
{
	return s[j + 1];
}

int call(_array const char *s)
	_requires(2 <= s._length)
	_ensures(return == 0)
{
	return c1(s);
}
