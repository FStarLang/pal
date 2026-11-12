#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* The fast strlen without `_pal_overread`: the word read must lie inside the
   array, which the loop cannot show for the word holding the terminator. */
typedef uint64_t __attribute__((__may_alias__)) word;

int all_nonzero(uint64_t x)
  _ensures(return == 0 || (x % 256 != 0 && x / 256 % 256 != 0 &&
                           x / 65536 % 256 != 0 && x / 16777216 % 256 != 0 &&
                           x / 4294967296 % 256 != 0 && x / 1099511627776 % 256 != 0 &&
                           x / 281474976710656 % 256 != 0 && x / 72057594037927936 % 256 != 0))
{
  return x % 256 != 0 && x / 256 % 256 != 0 &&
         x / 65536 % 256 != 0 && x / 16777216 % 256 != 0 &&
         x / 4294967296 % 256 != 0 && x / 1099511627776 % 256 != 0 &&
         x / 281474976710656 % 256 != 0 && x / 72057594037927936 % 256 != 0;
}

size_t word_strlen(_array const char *s)
  _requires(s._length <= 1000000 && (uintptr_t)s % 8 == 0)
  _requires(_exists(size_t i, i < s._length && s[i] == 0))
  _ensures(return < s._length && s[return] == 0)
  _ensures(_forall(size_t k, k < return ==> s[k] != 0))
{
  const char *a = s;
  const word *w;
  for (w = (const void *)s; all_nonzero(*w); w++)
    _invariant((uintptr_t)w % 8 == 0)
    _invariant(_forall(size_t k, k < (const char *)w - a && k < a._length ==> a[k] != 0));
  s = (const void *)w;
  for (; *s; s++)
    _invariant(_forall(size_t k, k < s - a && k < a._length ==> a[k] != 0));
  return s - a;
}
