#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* musl's wmemchr: the result is `s + i` for a computed `i` into a
   four-byte-element array. */
wchar_t *my_wmemchr(_array const wchar_t *s, wchar_t c, size_t n)
	_requires(n <= s._length)
	_ensures(return == 0 ==> _forall(size_t k, k < n ==> s[k] != c))
	_ensures(return != 0 ==> _exists(size_t i, i < n && return == (wchar_t *)(s + i)
		&& s[i] == c && _forall(size_t k, k < i ==> s[k] != c)))
{
	for (; n && *s != c; n--, s++)
		_invariant(s - _old(s) + n == _old(n))
		_invariant(_forall(_specint k, 0 <= k && k < s - _old(s) ==> _old(s)[k] != c));
	return n ? (wchar_t *)s : 0;
}

/* musl's wcsnlen: the pointer wmemchr returns is a pointer into `s`. */
size_t my_wcsnlen(_array const wchar_t *s, size_t n)
	_requires(n <= s._length && s._length <= 1000000)
	_ensures(return <= n)
	_ensures(_forall(size_t k, k < return ==> s[k] != 0))
	_ensures(return < n ==> s[return] == 0)
{
	const wchar_t *z = my_wmemchr(s, 0, n);
	if (z) n = z-s;
	return n;
}

/* And can be read through. */
wchar_t found_or_zero(_array const wchar_t *s, wchar_t c, size_t n)
	_requires(n <= s._length)
	_ensures(return == 0 || return == c)
{
	const wchar_t *z = my_wmemchr(s, c, n);
	if (z) return *z;
	return 0;
}

size_t my_wcslen(_array const wchar_t *s)
	_requires(_exists(size_t i, i < s._length && s[i] == 0))
	_requires(s._length <= 1000000)
	_ensures(return < s._length && s[return] == 0)
	_ensures(_forall(size_t k, k < return ==> s[k] != 0))
{
	const wchar_t *a;
	for (a=s; *s; s++)
		_invariant(s - a < a._length && _forall(_specint k, 0 <= k && k < s - a ==> a[k] != 0));
	return s-a;
}

/* musl's wcschr, for the terminator: `s` plus a computed count. */
wchar_t *wcs_end(_array const wchar_t *s)
	_requires(_exists(size_t i, i < s._length && s[i] == 0))
	_requires(s._length <= 1000000)
	_ensures(_exists(size_t i, i < s._length && return == s + i && s[i] == 0))
{
	return (wchar_t *)s + my_wcslen(s);
}

/* musl's wmemset and wmemcpy (with the count tested before it is
   decremented): the array keeps its length across the loop without the
   invariant saying so, and `_old(d._length)` is the entry length. */
wchar_t *my_wmemset(_array wchar_t *d, wchar_t c, size_t n)
	_requires(n <= d._length)
	_ensures(d._length == _old(d._length))
	_ensures(return == d)
	_ensures(_forall(size_t k, k < n ==> d[k] == c))
{
	wchar_t *ret = d;
	for (; n; n--)
		_invariant(d - ret + n + 1 == _old(n) + 1 && _old(d._length) >= _old(n))
		_invariant(_forall(_specint k, 0 <= k && k < d - ret ==> ret[k] == c))
		*d++ = c;
	return ret;
}

wchar_t *my_wmemcpy(_array wchar_t *d, _array const wchar_t *s, size_t n)
	_requires(n <= d._length && n <= s._length)
	_ensures(d._length == _old(d._length))
	_ensures(return == d)
	_ensures(_forall(size_t k, k < n ==> d[k] == s[k]))
{
	wchar_t *a = d;
	for (; n; n--)
		_invariant(d - a == s - _old(s) && d - a + n == _old(n))
		_invariant(_forall(_specint k, 0 <= k && k < d - a ==> a[k] == _old(s)[k]))
		*d++ = *s++;
	return a;
}

/* musl's strncmp, with `!n--` split so the count does not wrap: the
   walked pointers view the `char` arrays as `unsigned char`. */
int my_strncmp(_array const char *_l, _array const char *_r, size_t n)
	_requires(n == 0 || _exists(size_t i, i < n && i < _l._length && i < _r._length
		&& (i == n - 1 || _l[i] != _r[i] || _l[i] == 0)))
	_ensures(n == 0 ==> return == 0)
	_ensures(n != 0 ==> _exists(size_t i, i < n && i < _l._length && i < _r._length
		&& (i == n - 1 || _l[i] != _r[i] || _l[i] == 0)
		&& _forall(size_t k, k < i ==> _l[k] == _r[k] && _l[k] != 0)
		&& return == (int)(unsigned char)_l[i] - (int)(unsigned char)_r[i]))
{
	const unsigned char *l=(void *)_l, *r=(void *)_r;
	if (!n) return 0;
	n--;
	for (; *l && *r && n && *l == *r ; l++, r++, n--)
		_invariant(l - (const unsigned char *)_l == r - _r && l - _l + n + 1 == _old(n))
		_invariant(_forall(_specint k, 0 <= k && k < l - _l ==> _l[k] == _r[k] && _l[k] != 0));
	return *l - *r;
}

/* Integer type specifiers in any order. */
unsigned long widen(unsigned char c)
	_ensures(return == (long unsigned int)(char unsigned)c)
{
	return c;
}
