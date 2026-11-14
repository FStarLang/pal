/* Unsigned arithmetic in a contract is a number reduced modulo the type's
   range, so a quantifier over `d[m + k]` has no machine integer built from
   its own variable to trigger on. */
#include "pal.h"
#include <stddef.h>

void put(_array int *d, _array const int *s, size_t m, size_t n)
	_requires(m <= d._length && n <= s._length && m + n <= d._length)
	_ensures(d._length == _old(d._length))
	_ensures(_forall(size_t k, k < n ==> d[m + k] == s[k]))
	_ensures(_forall(size_t k, k < m ==> d[k] == _old(d[k])))
{
	for (size_t i = 0; i < n; i++)
		_invariant(i <= n && d._length == _old(d._length))
		_invariant(_forall(size_t k, k < i ==> d[m + k] == s[k]))
		_invariant(_forall(size_t k, k < m ==> d[k] == _old(d[k])))
		d[m + i] = s[i];
}
