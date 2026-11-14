#include <stddef.h>
#include "pal.h"

/* `s._length - k` in a contract (issue #449): `_length` is a `_specint`, so
   the difference is the mathematical one. */
int c1(_array const char *s) _requires(1 <= s._length - 1) _ensures(return == 0);
int c2(_array const char *s, size_t m)
	_requires(_exists(size_t k, k < s._length && 1 <= s._length - k)) _ensures(return == 0);

int c1(const char *s) { return 0; }
int c2(const char *s, size_t m) { return 0; }

/* `j < s._length - m` states `m + j < s._length` without `size_t`
   wraparound (musl's `strcat`). */
char at(_array const char *s, size_t m, size_t j)
	_requires(m <= s._length && j < s._length - m)
	_ensures(return == s[m + j])
{
	return s[m + j];
}

int use(_array const char *s)
	_requires(s._length >= 2)
	_ensures(return == 0)
{
	return c1(s);
}
