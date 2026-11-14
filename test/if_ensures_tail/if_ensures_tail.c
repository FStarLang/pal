#include "pal.h"
#include <stddef.h>

/* An annotated `if` at the end of an annotated `if`'s arm, the outer one
   directly followed by a loop (musl's strlcpy). Each `_ensures` is checked
   where it is written; neither is dropped. */
size_t nested(size_t n, size_t m)
	_requires(n < 100 && m < 100)
	_ensures(return <= 300)
{
	size_t x = n;
	if (m > 10)
		_ensures(x <= 200)
	{
		x = x + 1;
		if (m > 20)
			_ensures(x <= 200)
		{
			x = x + m;
		}
	}
	while (x > 300)
		_invariant(x <= 200)
		x--;
	return x;
}

/* An annotated `if` at the end of a loop body. */
size_t body(size_t n)
	_requires(n < 100)
{
	size_t x = 0, i;
	for (i = 0; i < n; i++)
		_invariant(x <= i && i <= n)
	{
		if (i % 2)
			_ensures(x <= i + 1)
		{
			x = x + 1;
		}
	}
	while (x > 0)
		_invariant(x <= 100)
	{
		x--;
		if (x % 2)
			_ensures(x <= 100)
		{
			x = x - 1;
		}
	}
	return x;
}
