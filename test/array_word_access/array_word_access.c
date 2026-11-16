#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* Word-at-a-time access through byte arrays, as musl's optimized string
   functions do it: a walked `const unsigned char *` is cast to a pointer to a
   wider unsigned type, and `*w` reads (or writes) the elements at its
   position as one little-endian integer. */
typedef uint64_t __attribute__((__may_alias__)) word;

int has_byte(uint64_t x, unsigned char c)
  _ensures(return != 0 || (x % 256 != c && x / 256 % 256 != c &&
                             x / 65536 % 256 != c && x / 16777216 % 256 != c &&
                             x / 4294967296 % 256 != c && x / 1099511627776 % 256 != c &&
                             x / 281474976710656 % 256 != c && x / 72057594037927936 % 256 != c))
  _ensures(return == 0 || x % 256 == c || x / 256 % 256 == c ||
                             x / 65536 % 256 == c || x / 16777216 % 256 == c ||
                             x / 4294967296 % 256 == c || x / 1099511627776 % 256 == c ||
                             x / 281474976710656 % 256 == c || x / 72057594037927936 % 256 == c)
{
  return x % 256 == c || x / 256 % 256 == c ||
         x / 65536 % 256 == c || x / 16777216 % 256 == c ||
         x / 4294967296 % 256 == c || x / 1099511627776 % 256 == c ||
         x / 281474976710656 % 256 == c || x / 72057594037927936 % 256 == c;
}

size_t find(_array const unsigned char *s, size_t n, unsigned char c)
  _requires(n <= s._length)
  _ensures(return <= n && (return < n ==> s[return] == c))
  _ensures(_forall(size_t k, k < return ==> s[k] != c))
{
  size_t n0 = n;
  const unsigned char *p = s;
  for (; (uintptr_t)p % 8 && n && *p != c; p++, n--)
    _invariant(p - s + n == _old(n) && _forall(size_t k, k < p - s ==> s[k] != c));
  if (n && *p != c)
    _ensures(p - s + n == _old(n) && _forall(size_t k, k < p - s ==> s[k] != c))
  {
    const word *w;
    for (w = (const void *)p; n >= 8 && !has_byte(*w, c); w++, n -= 8)
      _invariant((const unsigned char *)w - s + n == _old(n) && (uintptr_t)w % 8 == 0)
      _invariant(_forall(size_t k, k < (const unsigned char *)w - s ==> s[k] != c));
    p = (const void *)w;
  }
  for (; n && *p != c; p++, n--)
    _invariant(p - s + n == _old(n) && _forall(size_t k, k < p - s ==> s[k] != c));
  return n0 - n;
}

void copy_words(_array unsigned char *d, _array const unsigned char *s, size_t n)
  _requires(n <= d._length && n <= s._length && n % 8 == 0)
  _requires((uintptr_t)d % 8 == 0 && (uintptr_t)s % 8 == 0)
  _ensures(_forall(size_t k, k < n ==> d[k] == s[k]))
{
  word *wd = (void *)d;
  const word *ws = (const void *)s;
  for (; n; n -= 8, wd++, ws++)
    _invariant((unsigned char *)wd - d + n == _old(n) && n % 8 == 0 && _old(n) <= d._length)
    _invariant((const unsigned char *)ws - s == (unsigned char *)wd - d)
    _invariant((uintptr_t)wd % 8 == 0 && (uintptr_t)ws % 8 == 0)
    _invariant(_forall(size_t k, k < (unsigned char *)wd - d ==> d[k] == s[k]))
    *wd = *ws;
}

void store_pair(_array unsigned char *dest, uint32_t v)
  _requires(9 <= dest._length && (uintptr_t)dest % 4 == 0)
  _ensures(dest[0] == v % 256 && dest[1] == v / 256 % 256 &&
           dest[2] == v / 65536 % 256 && dest[3] == v / 16777216)
  _ensures(dest[4] == v % 256 && dest[7] == v / 16777216)
  _ensures(dest[8] == _old(dest[8]))
{
  unsigned char *s = dest;
  *(uint32_t *)(s + 0) = v;
  s += 4;
  *(uint32_t *)s = v;
}

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
  _pal_overread const word *w;
  for (w = (const void *)s; all_nonzero(*w); w++)
    _invariant((uintptr_t)w % 8 == 0)
    _invariant(_forall(size_t k, k < (const char *)w - a && k < a._length ==> a[k] != 0));
  s = (const void *)w;
  for (; *s; s++)
    _invariant(_forall(size_t k, k < s - a && k < a._length ==> a[k] != 0));
  return s - a;
}
