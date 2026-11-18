#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <wchar.h>

/* `n` wide chars are copied into a block of `n + 1`: the last cell is never
   written, so the array cannot be handed back as initialised. */
_allocated _nullable _array wchar_t *dup_wide(_array const wchar_t *s, size_t n)
	_requires(n < s._length)
	_ensures(return != 0 ==> return._length == n + 1)
{
	wchar_t *d = malloc((n + 1) * sizeof(wchar_t));
	if (!d) return NULL;
	return wmemcpy(d, s, n);
}
