#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* `seen` ends up marking exactly the bytes of `c`. The second invariant has
   the shape that loops when the solver picks its own trigger, `SizeT.v b`:
   each instance yields a fresh `j`, another `size_t` to instantiate every
   such quantifier on again. Its trigger keeps it to reads of `seen`. */
void mark(_array unsigned char *seen, _array const unsigned char *c)
	_requires(seen._length == 256)
	_requires(_forall(size_t k, k < 256 ==> seen[k] == 0))
	_requires(_exists(size_t i, i < c._length && c[i] == 0))
	_ensures(seen._length == 256)
	_ensures(_forall(size_t b, _trigger(seen[b]), b < 256 && seen[b] != 0 ==> _exists(size_t j, j < c._length && c[j] == b)))
{
	for (; *c; c++)
		_invariant(seen._length == 256)
		_invariant(_forall(size_t j, _trigger(_old(c)[j]), j < c - _old(c) ==> _old(c)[j] != 0 && seen[_old(c)[j]] != 0))
		_invariant(_forall(size_t b, _trigger(seen[b]), b < 256 && seen[b] != 0 ==> _exists(size_t j, j < c - _old(c) && _old(c)[j] == b)))
		_invariant(_exists(size_t i, c - _old(c) <= i && i < _old(c)._length && _old(c)[i] == 0))
		seen[*c] = 1;
}

/* A trigger on an `_exists`, in an `_assert`; a multi-pattern (both terms
   together) and alternatives (either `_trigger`). */
size_t find(_array const unsigned char *s, _array const unsigned char *t, size_t n)
	_requires(s._length == n && t._length == n)
	_requires(_exists(size_t i, _trigger(s[i]), i < n && s[i] == 0))
	_requires(_forall(size_t k, _trigger(s[k], t[k]), k < n ==> s[k] == t[k]))
	_ensures(return < n && t[return] == 0)
{
	size_t i = 0;
	while (s[i])
		_invariant(i < n)
		_invariant(_exists(size_t m, _trigger(s[m]), _trigger(t[m]), i <= m && m < n && s[m] == 0))
		i++;
	_assert(_forall(size_t k, _trigger(t[k]), k < n ==> t[k] == s[k]));
	return i;
}
