#include "pal.h"
#include <stddef.h>

/* An array argument that points into the middle of the caller's array (a
   walked pointer, or `base + i`) lends the caller's suffix from there on. */

wchar_t *wmemset(_array wchar_t *d, wchar_t c, size_t n)
	_requires(n <= d._length)
	_ensures(return == d)
	_ensures(d._length == _old(d._length))
	_ensures(_forall(size_t k, k < n ==> d[k] == c))
	_ensures(_forall(size_t k, n <= k && k < d._length ==> d[k] == _old(d[k])));

/* musl's wcsncpy: zero-fill the rest through the walked `d`. */
wchar_t *wcsncpy(_array wchar_t *restrict d, _array const wchar_t *restrict s, size_t n)
	_requires(n <= d._length)
	_requires(_exists(size_t i, i <= n && i <= s._length
		&& (i == n || (i < s._length && s[i] == 0))
		&& _forall(size_t k, k < i ==> s[k] != 0)))
	_ensures(return == d)
	_ensures(d._length == _old(d._length))
	_ensures(_exists(size_t i, i <= n && i <= s._length
		&& (i == n || (i < s._length && s[i] == 0))
		&& _forall(size_t k, k < i ==> s[k] != 0 && d[k] == s[k])
		&& _forall(size_t k, i <= k && k < n ==> d[k] == 0)))
{
	wchar_t *a = d;
	while (n && *s)
		_invariant(d - a == s - _old(s) && d - a + n == _old(n) && a._length == _old(d._length))
		_invariant(_forall(_specint k, 0 <= k && k < d - a ==> a[k] == _old(s)[k] && _old(s)[k] != 0))
		n--, *d++ = *s++;
	wmemset(d, 0, n);
	return a;
}

size_t wcslen(_array const wchar_t *s)
	_requires(_exists(size_t i, i < s._length && s[i] == 0))
	_requires(s._length <= 1000000)
	_ensures(return < s._length && s[return] == 0)
	_ensures(_forall(size_t k, k < return ==> s[k] != 0));

wchar_t *wcscpy(_array wchar_t *restrict d, _array const wchar_t *restrict s)
	_requires(_exists(size_t i, i < s._length && i < d._length && s[i] == 0
		&& _forall(size_t k, k < i ==> s[k] != 0)))
	_ensures(return == d)
	_ensures(d._length == _old(d._length))
	_ensures(_exists(size_t i, i < s._length && i < d._length && s[i] == 0
		&& _forall(size_t k, k < i ==> s[k] != 0)
		&& _forall(size_t k, k <= i ==> d[k] == s[k])
		&& _forall(size_t k, i < k && k < d._length ==> d[k] == _old(d[k]))));

/* musl's wcscat: copy behind the terminator found by wcslen. */
wchar_t *wcscat(_array wchar_t *restrict dest, _array const wchar_t *restrict src)
	_requires(dest._length <= 1000000)
	_requires(_exists(size_t m, m < dest._length && dest[m] == 0
		&& _forall(size_t k, k < m ==> dest[k] != 0)
		&& _exists(size_t j, j < src._length && m + j < dest._length && src[j] == 0
			&& _forall(size_t k, k < j ==> src[k] != 0))))
	_ensures(return == dest)
	_ensures(dest._length == _old(dest._length))
	_ensures(_exists(size_t m, m < dest._length && _old(dest[m]) == 0
		&& _forall(size_t k, k < m ==> _old(dest[k]) != 0 && dest[k] == _old(dest[k]))
		&& _exists(size_t j, j < src._length && m + j < dest._length && src[j] == 0
			&& _forall(size_t k, k < j ==> src[k] != 0)
			&& _forall(size_t k, k <= j ==> dest[m + k] == src[k]))))
{
	wcscpy(dest + wcslen(dest), src);
	return dest;
}

/* A read-only array lent at an offset. */
wchar_t first(_array const wchar_t *s)
	_requires(0 < s._length)
	_ensures(return == s[0]);

wchar_t elem_at(_array const wchar_t *s, size_t i)
	_requires(i < s._length)
	_ensures(return == s[i])
{
	return first(s + i);
}
