#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* musl's wcscpy: both pointers advance in the loop condition, so the loop
   writes them even though its body is empty. */
wchar_t *wcscpy(_array wchar_t *restrict d, _array const wchar_t *restrict s)
  _requires(_exists(size_t i, i < s._length && i < d._length && s[i] == 0
    && _forall(size_t k, k < i ==> s[k] != 0)))
  _ensures(return == d)
  _ensures(d._length == _old(d._length))
  _ensures(_exists(size_t i, i < s._length && i < d._length && s[i] == 0
    && _forall(size_t k, k < i ==> s[k] != 0)
    && _forall(size_t k, k <= i ==> d[k] == s[k])))
{
  wchar_t *a = d;
  while ((*d++ = *s++))
    _invariant(d - a == s - _old(s))
    _invariant(_exists(size_t i, d - a <= i && i < _old(s)._length && i < a._length
      && _old(s)[i] == 0))
    _invariant(_forall(_specint k, 0 <= k && k < d - a ==>
      a[k] == _old(s)[k] && _old(s)[k] != 0));
  return a;
}

/* An alignment kept by a step of 8, with the modulus written as a `size_t`. */
void walk_aligned(_array const unsigned char *s, size_t n)
  _requires(s._length <= 1000000 && 8 * n <= s._length)
  _requires((uintptr_t)s % sizeof(size_t) == 0)
{
  const unsigned char *p = s;
  for (; n; n--, p += 8)
    _invariant((uintptr_t)p % sizeof(size_t) == 0)
    _invariant(p - s + 8 * n == 8 * _old(n));
}
