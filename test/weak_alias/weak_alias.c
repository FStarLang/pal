#include "pal.h"
#include <stddef.h>

#define weak_alias(old, new) \
	extern __typeof(old) new __attribute__((__weak__, __alias__(#old)))

/* Contract on the public name only, as a prepended spec header gives it. */
size_t my_strlen(_array const char *s)
	_requires(s._length <= 1000000)
	_requires(_exists(size_t i, i < s._length && s[i] == 0))
	_ensures(return < s._length && s[return] == 0)
	_ensures(_forall(size_t k, k < return ==> s[k] != 0));

size_t __my_strlen(const char *s);

size_t __my_strlen(const char *s)
{
	const char *a = s;
	for (; *s; s++)
		_invariant(s - a < a._length)
		_invariant(_forall(_specint k, 0 <= k && k < s - a ==> a[k] != 0));
	return s - a;
}

weak_alias(__my_strlen, my_strlen);

/* Contract on the definition; the alias inherits it. */
int __twice(int x)
	_requires(x <= 1000 && x >= -1000)
	_ensures(return == 2 * x)
{
	return x + x;
}

weak_alias(__twice, twice);

int use(_array const char *s)
	_requires(s._length <= 1000000)
	_requires(_exists(size_t i, i < s._length && s[i] == 0))
	_ensures(return == 8)
{
	size_t n = my_strlen(s);
	size_t m = __my_strlen(s);
	_assert(n == m || n != m);
	return twice(4);
}
