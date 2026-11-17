#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <wchar.h>

/* A fresh heap copy of the first `n + 1` wide chars of `s`, as musl's
   `wcsdup` makes it: `wmemcpy` counts elements, `malloc` bytes. */
_allocated _nullable _array wchar_t *dup_wide(_array const wchar_t *s, size_t n)
	_requires(n < s._length)
	_ensures(return != 0 ==> return._length == n + 1
		&& _forall(size_t k, k <= n ==> return[k] == s[k]))
{
	wchar_t *d = malloc((n + 1) * sizeof(wchar_t));
	if (!d) return NULL;
	return wmemcpy(d, s, n + 1);
}
