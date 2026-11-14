#include "pal.h"
#include <stddef.h>

/* musl's memchr: an `if` that may move `s` with a loop of its own, and no
   `else`, followed by the loop that finishes the scan. With no annotation on
   the `if`, the following loop's invariant is what both arms establish. */
size_t find(_array const unsigned char *src, unsigned char c, size_t n)
	_requires(n <= src._length)
	_ensures(return <= n)
	_ensures(_forall(size_t j, j < n - return ==> src[j] != c))
{
	const unsigned char *s = src;
	if (n && *s != c) {
		const unsigned char *w;
		for (w = s; n >= 2 && w[0] != c && w[1] != c; w += 2, n -= 2)
			_invariant(w - src + n == _old(n))
			_invariant(_forall(size_t j, j < w - src ==> src[j] != c));
		s = w;
	}
	for (; n && *s != c; s++, n--)
		_invariant(s - src + n == _old(n))
		_invariant(_forall(size_t j, j < s - src ==> src[j] != c));
	return n;
}
