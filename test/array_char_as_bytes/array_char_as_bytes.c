/* `char` arrays passed to `_array void *` parameters, through a byte view. */
#include "pal.h"
#include <stddef.h>

void *my_memchr(_array const void *src, int c, size_t n)
	_requires(n <= src._length)
	_ensures(return == 0 ==> _forall(size_t k, k < n
		==> ((const unsigned char *)src)[k] != (unsigned char)c))
	_ensures(return != 0 ==> _exists(size_t i, i < n
		&& return == (void *)((const unsigned char *)src + i)
		&& ((const unsigned char *)src)[i] == (unsigned char)c
		&& _forall(size_t k, k < i ==> ((const unsigned char *)src)[k] != (unsigned char)c)));

void *my_memcpy(_array void *restrict dest, _array const void *restrict src, size_t n)
	_requires(n <= dest._length && n <= src._length)
	_ensures(return == dest && dest._length == _old(dest._length))
	_ensures(_forall(size_t k, k < n ==> ((unsigned char *)dest)[k] == ((const unsigned char *)src)[k]))
	_ensures(_forall(size_t k, n <= k && k < dest._length ==> ((unsigned char *)dest)[k] == _old(((unsigned char *)dest)[k])));

size_t my_strnlen(_array const char *s, size_t n)
	_requires(n <= s._length && s._length <= 1000000)
	_ensures(return <= n && _forall(size_t k, k < return ==> s[k] != 0))
	_ensures(return < n ==> s[return] == 0)
{
	const char *p = my_memchr(s, 0, n);
	return p ? p-s : n;
}

/* A walked `char` pointer handed over at an offset. */
size_t after(_array const char *s, size_t n)
	_requires(0 < n && n <= s._length)
	_ensures(return <= 1)
{
	const char *p = s;
	p++;
	return my_memchr(p, 'x', n - 1) ? 0 : 1;
}

char *copy(_array char *restrict d, _array const char *restrict s, size_t n)
	_requires(n <= d._length && n <= s._length)
	_ensures(return == d && d._length == _old(d._length))
	_ensures(_forall(size_t k, k < n ==> d[k] == s[k]))
	_ensures(_forall(size_t k, n <= k && k < d._length ==> d[k] == _old(d[k])))
{
	my_memcpy(d, s, n);
	return d;
}
void *my_memrchr(_array const void *m, int c, size_t n)
	_requires(n <= m._length)
	_ensures(return == 0 ==> _forall(size_t k, k < n
		==> ((const unsigned char *)m)[k] != (unsigned char)c))
	_ensures(return != 0 ==> _exists(size_t i, i < n
		&& return == (void *)((const unsigned char *)m + i)
		&& ((const unsigned char *)m)[i] == (unsigned char)c
		&& _forall(size_t k, i < k && k < n ==> ((const unsigned char *)m)[k] != (unsigned char)c)));

char *last(_array const char *s, int c, size_t n)
	_requires(n <= s._length)
	_ensures(return == 0 ==> _forall(size_t k, k < n ==> (unsigned char)s[k] != (unsigned char)c))
	_ensures(return != 0 ==> _exists(size_t i, i < n && return == (char *)(s + i)
		&& (unsigned char)s[i] == (unsigned char)c))
{
	return my_memrchr(s, c, n);
}
