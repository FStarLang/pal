#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* `_array void *` is an array of `unsigned char`: the mem* functions'
   parameters, walked through `unsigned char *` locals and read in contracts
   as `((unsigned char *)p)[k]`. */

void *mset(_array void *dest, int c, size_t n)
	_requires(n <= dest._length)
	_ensures(return == dest)
	_ensures(dest._length == _old(dest._length))
	_ensures(_forall(size_t k, k < n ==> ((unsigned char *)dest)[k] == (unsigned char)c))
{
	unsigned char *s = dest;
	for (; n; n--, s++)
		_invariant(s - (unsigned char *)dest + n == _old(n))
		_invariant(_forall(_specint k, 0 <= k && k < s - (unsigned char *)dest ==>
			((unsigned char *)dest)[k] == (unsigned char)c))
		*s = c;
	return dest;
}
void *mcpy(_array void *restrict dest, _array const void *restrict src, size_t n)
	_requires(n <= dest._length && n <= src._length)
	_ensures(return == dest)
	_ensures(dest._length == _old(dest._length))
	_ensures(_forall(size_t k, k < n ==> ((unsigned char *)dest)[k] == ((const unsigned char *)src)[k]))
	_ensures(_forall(size_t k, n <= k && k < dest._length ==> ((unsigned char *)dest)[k] == _old(((unsigned char *)dest)[k])))
{
	unsigned char *d = dest;
	const unsigned char *s = src;
	for (; n; n--)
		_invariant(d - (unsigned char *)dest + n == _old(n) && s - (const unsigned char *)src == d - (unsigned char *)dest)
		_invariant(_forall(_specint k, 0 <= k && k < d - (unsigned char *)dest ==> ((unsigned char *)dest)[k] == ((const unsigned char *)src)[k]))
		_invariant(_forall(_specint k, 0 <= k && d - (unsigned char *)dest <= k && k < dest._length ==> ((unsigned char *)dest)[k] == _old(((unsigned char *)dest)[k])))
		*d++ = *s++;
	return dest;
}
void user(_array unsigned char *a, _array const unsigned char *b)
	_requires(a._length == 4 && b._length == 4)
	_ensures(_forall(size_t k, k < 4 ==> a[k] == b[k]))
{
	mcpy(a, b, 4);
}
