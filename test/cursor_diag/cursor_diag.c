#include "pal.h"
#include <stddef.h>
#include <stdint.h>

char *next(_cursor char **str)
  _requires(*str != 0 ==> (*str)._length > 0)
  _ensures(*str == 0);

/* `*str` after the call is the new position; its contents are `_old(*str)[k]`. */
char post_contents(_cursor char **str)
  _requires(*str != 0 ==> (*str)._length > 1)
  _ensures(*str != 0 ==> (*str)[0] == 0)
{
  return 0;
}

void caller(_array char *a)
  _requires(a._length > 0)
{
  char *p = a;
  next(&p);
}
