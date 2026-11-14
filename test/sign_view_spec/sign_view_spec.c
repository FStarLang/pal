#include "pal.h"
#include <stddef.h>

/* strverscmp's prefix loop: a local viewing a `char` array as `unsigned
   char` is subscripted in the invariant, and reads the same bytes at its
   own type. */
int prefix(_array const char *l0, _array const char *r0)
	_requires(_exists(size_t i, i < l0._length && l0[i] == 0))
	_requires(_exists(size_t i, i < r0._length && r0[i] == 0))
{
	const unsigned char *l = (const void *)l0;
	const unsigned char *r = (const void *)r0;
	size_t i;
	for (i = 0; l[i] == r[i]; i++)
		_invariant(i < l0._length && i < r0._length)
		_invariant(_forall(_specint k, 0 <= k && k < i ==> l[k] == r[k] && l[k] != 0))
	{
		if (!l[i]) return 0;
	}
	_assert(l[i] != r[i]);
	return l[i] - r[i];
}

/* A negative `char` is a byte above 127 through the view. */
void high(_array const char *s)
	_requires(1 <= s._length && s[0] == -1)
{
	const unsigned char *u = (const void *)s;
	_assert(_forall(size_t k, k < 1 ==> u[k] == 255));
}
