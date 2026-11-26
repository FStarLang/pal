#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* A word read through a `_pal_overread` pointer on the right of `&&` in a
   loop guard, as in musl's stpncpy and strlcpy: `n >= 8` is what keeps the
   read inside the array, so it must still guard the read. When the scan runs
   off the end, `w` reaches the end of `s` exactly as `n` reaches 0. */
typedef uint64_t __attribute__((__may_alias__)) word;

int all_nonzero(uint64_t x)
  _ensures(return == 0 || x % 256 != 0)
{
  return x % 256 != 0 && x / 256 % 256 != 0 &&
         x / 65536 % 256 != 0 && x / 16777216 % 256 != 0 &&
         x / 4294967296 % 256 != 0 && x / 1099511627776 % 256 != 0 &&
         x / 281474976710656 % 256 != 0 && x / 72057594037927936 % 256 != 0;
}

size_t word_prefix(_array const char *s, size_t n)
  _requires(n <= s._length && (uintptr_t)s % 8 == 0)
  _ensures(return <= n)
{
  _pal_overread const word *w;
  size_t m;
  for (w = (const void *)s, m = n; m >= sizeof(word) && all_nonzero(*w);
       w++, m -= sizeof(word))
    _invariant((uintptr_t)w % 8 == 0)
    _invariant((const char *)w - s + m == n);
  return n - m;
}
