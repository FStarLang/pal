#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* musl's string functions walk a pointer through the array instead of
   indexing it. The C below is musl's; only the annotations are added. A
   walked pointer's position in its array is `p - base` in a contract, and
   `p[k]` / `p._length` are relative to where it points. `memchr` and
   `memcpy` take `void *` in C; here they take the byte arrays musl casts
   those to. */

size_t wcslen(_array const wchar_t *s)
	_requires(_exists(size_t i, i < s._length && s[i] == 0))
	_requires(s._length <= 1000000)
	_ensures(return < s._length && s[return] == 0)
	_ensures(_forall(size_t k, k < return ==> s[k] != 0))
{
	const wchar_t *a;
	for (a=s; *s; s++)
		_invariant(s - a < _old(s)._length)
		_invariant(_forall(_specint k, 0 <= k && k < s - a ==> a[k] != 0));
	return s-a;
}

int strcmp(_array const char *l, _array const char *r)
	_requires(_exists(size_t i, i < l._length && l[i] == 0))
	_requires(_exists(size_t i, i < r._length && r[i] == 0))
	_ensures(_exists(size_t i, i < l._length && i < r._length
		&& (l[i] != r[i] || l[i] == 0)
		&& _forall(size_t k, k < i ==> l[k] == r[k] && l[k] != 0)
		&& return == (int)(unsigned char)l[i] - (int)(unsigned char)r[i]))
{
	for (; *l==*r && *l; l++, r++)
		_invariant(l - _old(l) == r - _old(r))
		_invariant(l - _old(l) < _old(l)._length && r - _old(r) < _old(r)._length)
		_invariant(_forall(_specint k, 0 <= k && k < l - _old(l) ==>
			_old(l)[k] == _old(r)[k] && _old(l)[k] != 0));
	return *(unsigned char *)l - *(unsigned char *)r;
}

void *byte_memchr(_array const unsigned char *src, int c, size_t n)
	_requires(src._length == n)
	_ensures(return == 0 ==> _forall(size_t k, k < n ==> src[k] != (unsigned char)c))
	_ensures(return != 0 ==> _exists(size_t i, i < n && return == (void *)(src + i)
		&& src[i] == (unsigned char)c
		&& _forall(size_t k, k < i ==> src[k] != (unsigned char)c)))
{
	const unsigned char *s = src;
	c = (unsigned char)c;
	for (; n && *s != c; s++, n--)
		_invariant((_specint)n == s._length && c == (unsigned char)_old(c))
		_invariant(_forall(_specint k, 0 <= k && k < s - src ==> src[k] != c));
	return n ? (void *)s : 0;
}

void *byte_memcpy(_array unsigned char *restrict dest, _array const unsigned char *restrict src, size_t n)
	_requires(dest._length == n && src._length == n)
	_ensures(_forall(_specint k, 0 <= k && k < (_specint)n ==> dest[k] == src[k]))
{
	unsigned char *d = dest;
	const unsigned char *s = src;
	for (; n; n--)
		_invariant(d - dest == s - src)
		_invariant((_specint)n == d._length && (_specint)n == s._length)
		_invariant(_forall(_specint k, 0 <= k && k < d - dest ==> dest[k] == src[k]))
		*d++ = *s++;
	return dest;
}

/* Walking backwards from one past the end. */
size_t count_back(_array const unsigned char *s, size_t n)
	_requires(s._length == n && n <= 1000000)
	_ensures(return == n)
{
	const unsigned char *p = s + n;
	size_t c = 0;
	while (p != s)
		_invariant(s <= p && p - s <= (_specint)n && (_specint)c + (p - s) == (_specint)n)
	{
		p--;
		c++;
	}
	return c;
}

/* Offsets in either direction from a pointer moved into the middle. */
int around(_array const int *a, size_t n)
	_requires(a._length == n && n >= 4)
	_ensures(return == (a[3] == a[1]))
{
	const int *p = a;
	p += 2;
	int x = *(p + 1);
	--p;
	return x == *p;
}

/* Positions mixed with `size_t` counts, both ways round. */
int wmemcmp(_array const wchar_t *l, _array const wchar_t *r, size_t n)
	_requires(n <= l._length && n <= r._length)
	_ensures(_exists(size_t i, i <= n
		&& _forall(size_t k, k < i ==> l[k] == r[k])
		&& (i == n ==> return == 0)
		&& (i < n ==> l[i] != r[i]
			&& (l[i] < r[i] ==> return == -1)
			&& (l[i] > r[i] ==> return == 1))))
{
	for (; n && *l==*r; n--, l++, r++)
		_invariant(n <= _old(n) && l - _old(l) == r - _old(r) && l - _old(l) == _old(n) - n)
		_invariant(_forall(_specint k, 0 <= k && k < l - _old(l) ==>
			_old(l)[k] == _old(r)[k]));
	return n ? (*l < *r ? -1 : *l > *r) : 0;
}

int wcsncmp(_array const wchar_t *l, _array const wchar_t *r, size_t n)
	_requires(n <= l._length && n <= r._length)
	_ensures(_exists(size_t i, i <= n
		&& _forall(size_t k, k < i ==> l[k] == r[k] && l[k] != 0)
		&& (i == n ==> return == 0)
		&& (i < n ==> (l[i] != r[i] || l[i] == 0)
			&& (l[i] < r[i] ==> return == -1)
			&& (l[i] > r[i] ==> return == 1)
			&& (l[i] == r[i] ==> return == 0))))
{
	for (; n && *l==*r && *l && *r; n--, l++, r++)
		_invariant(l - _old(l) == r - _old(r) && (l - _old(l)) + n == _old(n))
		_invariant(_forall(size_t k, k < l - _old(l) ==>
			_old(l)[k] == _old(r)[k] && _old(l)[k] != 0))
		_invariant(_exists(size_t i, l - _old(l) <= i && i <= _old(n)));
	return n ? (*l < *r ? -1 : *l > *r) : 0;
}

/* A three-way result, with the stopping position named in an assertion. */
int wcscmp(_array const wchar_t *l, _array const wchar_t *r)
	_requires(_exists(size_t i, i < l._length && l[i] == 0))
	_requires(_exists(size_t i, i < r._length && r[i] == 0))
	_ensures(_exists(size_t i, i < l._length && i < r._length
		&& (l[i] != r[i] || l[i] == 0)
		&& _forall(size_t k, k < i ==> l[k] == r[k] && l[k] != 0)
		&& (l[i] < r[i] ==> return == -1)
		&& (l[i] > r[i] ==> return == 1)
		&& (l[i] == r[i] ==> return == 0)))
{
	for (; *l==*r && *l && *r; l++, r++)
		_invariant(l - _old(l) == r - _old(r))
		_invariant(l - _old(l) < _old(l)._length && r - _old(r) < _old(r)._length)
		_invariant(_forall(_specint k, 0 <= k && k < l - _old(l) ==>
			_old(l)[k] == _old(r)[k] && _old(l)[k] != 0));
	_assert(_exists(size_t i, (_specint)i == l - _old(l)));
	return *l < *r ? -1 : *l > *r;
}

/* A `size_t` quantifier bounded by a position. */
size_t wcslen_sized(_array const wchar_t *s)
	_requires(_exists(size_t i, i < s._length && s[i] == 0))
	_requires(s._length <= 1000000)
	_ensures(return < s._length && s[return] == 0)
	_ensures(_forall(size_t k, k < return ==> s[k] != 0))
{
	const wchar_t *a;
	for (a=s; *s; s++)
		_invariant(s - a < _old(s)._length)
		_invariant(_forall(size_t k, k < s - a ==> a[k] != 0));
	return s-a;
}

/* A conversion that keeps every distance, to a wide signed type, is read
   through. */
size_t count_wide(_array const unsigned char *s, size_t n)
	_requires(s._length == n && n <= 1000000)
	_ensures(return == n)
{
	const unsigned char *p = s;
	size_t c = 0;
	while (c < n)
		_invariant(c <= n && (int64_t)(p - s) == (_specint)c)
	{
		p++;
		c++;
	}
	return c;
}
