#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* The second conjunct is not preserved: the failure is reported against that
   conjunct alone. */
size_t zeros(_array const uint8_t *s, size_t n)
  _requires(n <= s._length)
{
  size_t i = 0, z = 0;
  while (i < n)
    _invariant(i <= n && z == 0 && z <= i)
  {
    if (s[i] == 0)
      z++;
    i++;
  }
  return z;
}
