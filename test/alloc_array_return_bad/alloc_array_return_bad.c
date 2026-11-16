#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* The last cell is never written: a fresh block's cells hold no value, so
   the array cannot be handed back as initialised. */
_allocated _nullable _array char *copy_prefix(_array const char *s, size_t n)
	_requires(n < s._length)
	_ensures(return != 0 ==> return._length == n + 1)
{
	char *d = malloc(n + 1);
	if (!d) return 0;
	memcpy(d, s, n);
	return d;
}
