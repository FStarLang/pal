#include "pal.h"
#include <stddef.h>

// The contract is on the first declaration; later redeclarations, as in a
// system header that is included after a spec header, inherit it from clang
// and must not be compared as if they had restated it.
size_t count(_array const int *s, size_t n)
	_requires(n <= s._length)
	_ensures(return == n);

size_t count(const int *, size_t);
size_t count(const int *a, size_t m);

size_t count(const int *s, size_t n)
{
	if (n > 0)
		(void)s[n - 1];
	return n;
}

size_t twice(_array const int *s)
	_requires(s._length == 4)
	_ensures(return == 8)
{
	return count(s, 4) + count(s, 4);
}
