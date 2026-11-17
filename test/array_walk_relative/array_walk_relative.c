#include "pal.h"
#include <stddef.h>

/* musl's __stpcpy, byte loop: both array parameters are walked and no
   local keeps the base. `d[k - (d - _old(d))]` is the array's current
   element `k` counted from the entry position: a `_specint` subscript may be
   negative relative to where `d` points now. */
char *cpy(_array char *restrict d, _array const char *restrict s)
	_requires(_exists(size_t i, i < s._length && i < d._length && s[i] == 0
		&& _forall(size_t k, k < i ==> s[k] != 0)))
	_ensures(d._length == _old(d._length))
	_ensures(_forall(size_t i, i < s._length && s[i] == 0 && _forall(size_t k, k < i ==> s[k] != 0)
		==> i < d._length && return == (char *)(d + i)
		&& _forall(size_t k, k <= i ==> d[k] == s[k])
		&& _forall(size_t k, i < k && k < d._length ==> d[k] == _old(d[k]))))
{
	for (; (*d=*s); s++, d++)
		_invariant(d - _old(d) == s - _old(s))
		_invariant(_exists(size_t i, s - _old(s) <= i && i < _old(s)._length && i < _old(d)._length && _old(s)[i] == 0
			&& _forall(size_t k, k < i ==> _old(s)[k] != 0)))
		_invariant(_forall(_specint k, 0 <= k && k < d - _old(d) ==> d[k - (d - _old(d))] == _old(s)[k]))
		_invariant(_forall(_specint k, d - _old(d) <= k && k < _old(d)._length ==> d[k - (d - _old(d))] == _old(d[k])))
		;
	return d;
}
