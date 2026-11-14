#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* A fresh heap copy of the first `n` chars of `s`, terminated. */
_allocated _nullable _array char *copy_prefix(_array const char *s, size_t n)
	_requires(n < s._length)
	_ensures(return != 0 ==> return._length == n + 1 && return[n] == 0
		&& _forall(size_t k, k < n ==> return[k] == s[k]))
{
	char *d = malloc(n + 1);
	if (!d) return 0;
	memcpy(d, s, n);
	d[n] = 0;
	return d;
}

/* The same copy, returning `memcpy`'s value, which is `d`. */
_allocated _nullable _array unsigned char *dup_bytes(_array const unsigned char *s, size_t n)
	_requires(n <= s._length && n > 0)
	_ensures(return != 0 ==> return._length == n
		&& _forall(size_t k, k < n ==> return[k] == s[k]))
{
	unsigned char *d = malloc(n);
	if (!d) return 0;
	return memcpy(d, s, n);
}
