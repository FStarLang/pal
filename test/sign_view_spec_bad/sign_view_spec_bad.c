#include "pal.h"
#include <stddef.h>

/* Through an `unsigned char` view a negative `char` is not below 128. */
void high(_array const char *s)
	_requires(1 <= s._length && s[0] == -1)
{
	const unsigned char *u = (const void *)s;
	_assert(_forall(size_t k, k < 1 ==> u[k] < 128));
}
