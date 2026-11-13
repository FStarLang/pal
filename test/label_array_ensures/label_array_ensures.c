#include "pal.h"
#include <stddef.h>

/* A forward `goto` to a label whose `_ensures` talks about array contents
   through a local alias, `_length`, `_old(p)[k]` and `_old(p[k])`, modelled
   on musl's strlcpy. */
size_t copy3(_array char *d, _array const char *s, size_t n)
	_requires(3 <= d._length && 3 <= s._length)
	_ensures(d._length == _old(d._length))
	_ensures(n >= 3 ==> _forall(size_t j, j < 3 ==> d[j] == s[j]))
	_ensures(n < 3 ==> _forall(size_t j, j < d._length ==> d[j] == _old(d[j])))
{
	char *d0 = d;
	if (n < 3) goto finish;
	for (; d - d0 < 3; d++, s++)
		_invariant(d - d0 == s - _old(s) && d - d0 <= 3 && d0._length == _old(d._length))
		_invariant(_forall(size_t j, j < d - d0 ==> d0[j] == _old(s)[j]))
		*d = *s;
finish: _ensures(d0._length == _old(d._length))
	_ensures(_old(n) >= 3 ==> _forall(size_t j, j < 3 ==> d0[j] == _old(s)[j]))
	_ensures(_old(n) < 3 ==> _forall(size_t j, j < d0._length ==> d0[j] == _old(d[j])))
	_ensures(_old(n) < 3 ==> d == d0)
	return d - d0;
}
