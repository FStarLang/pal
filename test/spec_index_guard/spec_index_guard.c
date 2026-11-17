/* `_specint` subscripts whose lower bound is not syntactically 0. */
#include "pal.h"
#include <stddef.h>
#include <wchar.h>

wchar_t *wfill(_array wchar_t *d, wchar_t c, size_t n)
	_requires(n <= d._length)
	_ensures(return == d && d._length == _old(d._length))
	_ensures(_forall(size_t k, k < n ==> d[k] == c))
	_ensures(_forall(size_t k, n <= k && k < d._length ==> d[k] == _old(d[k])))
{
	wchar_t *a = d;
	for (; n; n--)
		_invariant(d - a + n == _old(n))
		_invariant(_forall(_specint k, 0 <= k && k < d - a ==> a[k] == c))
		_invariant(_forall(_specint k, d - a <= k && k < a._length ==> a[k] == _old(d[k])))
		*d++ = c;
	return a;
}
