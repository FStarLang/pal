#include "pal.h"
#include <stddef.h>
#include <wchar.h>

/* `wchar_t *a = d;` before `d` moves holds the array's base for the whole
   body, so `a[k]` is indexed exactly as the contract's `d[k]`: a quantified
   `_assert` through `a` is the same term the `_ensures` needs. */

wchar_t *append(_array wchar_t *restrict d, _array const wchar_t *restrict s, size_t m, size_t n)
	_requires((_specint)m + n < d._length && n <= s._length)
	_ensures(return == d)
	_ensures(d._length == _old(d._length))
	_ensures(_exists(size_t j, j == (_specint)m + n
		&& _forall(size_t k, k < m ==> d[k] == _old(d[k]))
		&& _forall(size_t k, k < n ==> d[(_specint)m + k] == s[k])
		&& d[j] == 0
		&& _forall(size_t k, j < k && k < d._length ==> d[k] == _old(d[k]))))
{
	wchar_t *a = d;
	d += m;
	while (n)
		_invariant(a._length == _old(d._length) && s - _old(s) + n == _old(n))
		_invariant(d - a == m + (s - _old(s)))
		_invariant(_forall(size_t k, k < m ==> a[k] == _old(d[k])))
		_invariant(_forall(size_t k, k < s - _old(s) ==> a[(_specint)m + k] == _old(s)[k]))
		_invariant(_forall(size_t k, d - a <= k && k < a._length ==> a[k] == _old(d[k])))
	{
		n--, *d++ = *s++;
	}
	*d = 0;
	_assert(_exists(size_t j, j == d - a
		&& _forall(size_t k, k < m ==> a[k] == _old(d[k]))
		&& _forall(size_t k, k < s - _old(s) ==> a[(_specint)m + k] == _old(s)[k])
		&& a[j] == 0
		&& _forall(size_t k, j < k && k < a._length ==> a[k] == _old(d[k]))));
	return a;
}
