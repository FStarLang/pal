#include "pal.h"
#include <stddef.h>
size_t wcslen(_array const wchar_t *s)
	_requires(_exists(size_t i, i < s._length && s[i] == 0))
	_requires(s._length <= 1000000)
	_ensures(return < s._length && s[return] == 0)
	_ensures(_forall(size_t k, k < return ==> s[k] != 0));

wchar_t *wcschr(_array const wchar_t *s, wchar_t c)
	_requires(_exists(size_t i, i < s._length && s[i] == 0))
	_requires(s._length <= 1000000)
	_ensures(_exists(size_t i, i < s._length && (s[i] == c || s[i] == 0)
		&& _forall(size_t k, k < i ==> s[k] != c && s[k] != 0)
		&& (s[i] == c ==> return != 0 && return == (wchar_t *)(s + i))
		&& (s[i] != c ==> return == 0)));

size_t wcscspn(_array const wchar_t *s, _array const wchar_t *c)
	_requires(_exists(size_t i, i < s._length && s[i] == 0))
	_requires(_exists(size_t i, i < c._length && c[i] == 0
		&& _forall(size_t l, l < i ==> c[l] != 0)))
	_requires(s._length <= 1000000 && c._length <= 1000000)
	_ensures(return < s._length)
	_ensures(_exists(_specint m, 0 <= m && m < c._length && c[m] == 0
		&& _forall(size_t l, l < m ==> c[l] != 0)
		&& _forall(size_t k, k < return ==> s[k] != 0
			&& _forall(size_t l, l < m ==> c[l] != s[k]))
		&& (s[return] == 0 || _exists(size_t l, l < m && c[l] == s[return]))))
{
	const wchar_t *a;
	if (!c[0]) return wcslen(s);
	if (!c[1]) return (s=wcschr(a=s, *c)) ? s-a : wcslen(a);
	for (a=s; *s && !wcschr(c, *s); s++)
		_invariant(_exists(size_t i, s - a <= i && i < a._length && a[i] == 0))
		_invariant(_exists(size_t m, m < c._length && c[m] == 0
			&& _forall(size_t l, l < m ==> c[l] != 0)
			&& _forall(_specint k, 0 <= k && k < s - a ==> a[k] != 0
				&& _forall(size_t l, l < m ==> c[l] != a[k]))));
	_assert(_exists(size_t m, m < c._length && c[m] == 0 && _forall(size_t l, l < m ==> c[l] != 0)));
	_assert(*s == 0 || _exists(size_t i, i < c._length && c[i] == *s && _forall(size_t l, l < i ==> c[l] != 0)));
	return s-a;
}
