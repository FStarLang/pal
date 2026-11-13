#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* musl's wmemmove: each arm of the `if` is a copy loop, and the `return`
   after it needs what either loop established. The `return` is copied into
   both arms, so no join of the two loops' exit states is needed. (`n--`
   in the condition wraps on exit, which size_t arithmetic here rejects.) */
int *move(_array int *d, _array const int *s, size_t n)
	_requires(n <= d._length && n <= s._length && d != s)
	_ensures(return == d)
	_ensures(d._length == _old(d._length))
	_ensures(_forall(size_t k, k < n ==> d[k] == s[k]))
	_ensures(_forall(size_t k, n <= k && k < d._length ==> d[k] == _old(d[k])))
{
	int *d0 = d;
	if (d == s) return d;
	if ((uintptr_t)d-(uintptr_t)s < n * sizeof *d)
		while (n)
			_invariant(n <= _old(n) && d._length == _old(d._length))
			_invariant(_forall(_specint k, 0 <= k && n <= k && k < _old(n) ==> d[k] == s[k]))
			_invariant(_forall(_specint k, 0 <= k && k < n ==> d[k] == _old(d[k])))
			_invariant(_forall(_specint k, _old(n) <= k && k < d._length ==> d[k] == _old(d[k])))
		{ n--; d[n] = s[n]; }
	else
		while (n)
			_invariant(d - d0 == s - _old(s) && d - d0 + n == _old(n) && (_specint)n <= d._length && (_specint)n <= s._length && d0._length == _old(d._length))
			_invariant(_forall(_specint k, 0 <= k && k < d - d0 ==> d0[k] == _old(s)[k]))
			_invariant(_forall(_specint k, 0 <= k && d - d0 <= k && k < d0._length ==> d0[k] == _old(d[k])))
		{ n--; *d++ = *s++; }
	return d0;
}
