/* Contracts apply C's integer promotions; a local aliasing an `_array void *`
   parameter is subscripted and offset like a typed array. */
#include "pal.h"
#include <stddef.h>
#include <stdint.h>

int diff(unsigned char a, unsigned char b)
	_ensures(return == a - b)
{
	return a - b;
}

int cmp_bytes(_array const void *vl, _array const void *vr, size_t i)
	_requires(i < vl._length && i < vr._length)
	_ensures(return == ((const unsigned char *)vl)[i] - ((const unsigned char *)vr)[i])
{
	const unsigned char *l = vl, *r = vr;
	return l[i] - r[i];
}

int neg(uint8_t a)
	_ensures(return == -a)
	_ensures(a > 0 ==> return < 0)
{
	return -a;
}

_Bool mixed(uint8_t a, int8_t b)
	_requires(a == 255 && b == -1)
	_ensures(return == 0)
	_ensures(a != b)
{
	return a == b;
}

const void *last_at(_array const void *m, int c, size_t n)
	_requires(0 < n && n <= m._length)
	_ensures(return == 0 || n > 0 && ((const unsigned char *)m)[n - 1] == (unsigned char)c)
{
	const unsigned char *s = m;
	c = (unsigned char)c;
	if (s[n-1]==c) return (const void *)(s+(n-1));
	return 0;
}
