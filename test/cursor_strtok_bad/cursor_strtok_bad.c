#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* Reads `*p` when `s` is not null, where the caller need not have stored
   anything in it yet (the first call of `strtok_r(str, sep, &save)`). */
char *tok_bad(_nullable _array char *restrict s, _cursor_from(s) char **restrict p)
  _requires(*p != 0 ==> (*p)._length <= PTRDIFF_MAX
    && _exists(size_t i, i < (*p)._length && (*p)[i] == 0))
{
	char *t = *p;
	if (!s) return t;
	*p = t;
	return s;
}
