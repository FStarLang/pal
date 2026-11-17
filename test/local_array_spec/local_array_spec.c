#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "pal.h"

#define BITOP(a,b,op) \
 ((a)[(size_t)(b)/64] op (size_t)1<<((size_t)(b)%64))

/* strspn's byte set: a local array named in an invariant and an assertion. */
size_t count(_array const unsigned char *c, size_t n)
	_requires(1 <= n && n <= c._length)
{
	size_t bs[4] = { 0 };
	size_t i;
	_assert(bs[0] == 0 && bs[3] == 0);
	for (i = 0; i < n; i++)
		_invariant(i <= n && bs[1] == i && bs[3] == 0)
	{
		bs[1]++;
	}
	BITOP(bs, c[0] % 2, |=);
	_assert(((bs[(c[0] % 2) / 64] >> ((c[0] % 2) % 64)) & 1) != 0);
	_assert(bs[1] == n && bs[3] == 0);
	return bs[1];
}

/* strcspn's: cleared with memset, then named after an `if` and at a label. */
size_t cleared(size_t x)
{
	size_t bs[4];
	memset(bs, 0, sizeof bs);
	_assert(_forall(size_t k, k < 4 ==> bs[k] == 0));
	if (x)
		_ensures(bs[0] == x && bs[1] == 0)
	{
		bs[0] = x;
	}
	if (!x) goto done;
	bs[2] = 1;
done: _ensures(bs[0] == x && bs[1] == 0)
	return bs[0];
}
