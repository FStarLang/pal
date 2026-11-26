#include "pal.h"
#include <stddef.h>

/* `_Bool` equality is `<==>`, under which neither side implies the guards of
   its own `&&`, `||` or `==>`: `s[5]` is out of bounds where it is
   evaluated, so each postcondition is undefined and must not verify. */

_Bool iff_and(_array char *s, int x)
  _requires(s._length == 3 && x == 1)
  _ensures(return == (x == 1 && s[5] == 0))
{
  return 0;
}

_Bool iff_or(_array char *s, int x)
  _requires(s._length == 3 && x == 1)
  _ensures(return == (x != 1 || s[5] == 0))
{
  return 0;
}

_Bool iff_implies(_array char *s, int x)
  _requires(s._length == 3 && x == 1)
  _ensures((x == 1 ==> s[5] == 0) == return)
{
  return 0;
}
