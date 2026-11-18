#include "pal.h"
#include <stddef.h>
#include <sys/types.h>

/* A local that views an `_array` at the other signedness of char: reads and
   writes through it mean the reinterpreted byte. Modelled on musl's swab
   (void array seen as char) and strverscmp (char array seen as unsigned
   char). */
void swap2(_array const void *_src, _array void *_dest, ssize_t n)
	_requires(2 <= _src._length && 2 <= _dest._length)
	_requires(n <= 0 || (size_t)n <= _dest._length)
	_ensures(((unsigned char *)_dest)[0] == ((const unsigned char *)_src)[1])
	_ensures(((unsigned char *)_dest)[1] == ((const unsigned char *)_src)[0])
	_ensures(_dest._length == _old(_dest._length))
{
	const char *src = _src;
	char *dest = _dest;
	_assert(n < 0 || (size_t)n == n);
	dest[0] = src[1];
	dest++;
	*dest = src[0];
}

/* A write through a walked pointer at the other signedness. */
void clear(_array char *_d, size_t n)
	_requires(n <= _d._length)
	_ensures(_forall(size_t k, k < n ==> _d[k] == 0))
{
	unsigned char *d = (void *)_d;
	for (; n; n--, d++)
		_invariant(d - _d + n == _old(n) && _d._length == _old(_d._length))
		_invariant(_forall(size_t k, k < d - _d ==> _d[k] == 0))
		*d = 0;
}

int cmp(_array const char *l0, _array const char *r0)
	_requires(_exists(size_t i, i < l0._length && l0[i] == 0))
	_requires(_exists(size_t i, i < r0._length && r0[i] == 0))
	_ensures(return != 0 || _exists(size_t i, i < l0._length && l0[i] == 0 && r0[i] == 0))
{
	const unsigned char *l = (const void *)l0;
	const unsigned char *r = (const void *)r0;
	size_t i, dp;
	for (dp = i = 0; l[i] == r[i]; i++)
		_invariant(i < l0._length && i < r0._length && dp <= i)
		_invariant(_forall(_specint k, 0 <= k && k < i ==> l0[k] == r0[k] && l0[k] != 0))
	{
		int c = l[i];
		if (!c) return 0;
		if (c > '9') dp = i + 1;
	}
	return 1;
}
