#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* Each conjunct of the invariant is asserted on its own at the end of an
   iteration; a later one may rely on an earlier one to be well defined
   (`s[i - 1]` needs `0 < i`), and conjuncts may quantify over the array or
   name the walked pointer. */
size_t zeros(_array const uint8_t *s, size_t n)
  _requires(n <= s._length)
  _ensures(return <= n)
{
  size_t i = 0, z = 0;
  while (i < n)
    _invariant(i <= n && z <= i)
    _invariant(i == 0 || (0 < i && (s[i - 1] == 0 || s[i - 1] != 0)))
    _invariant(_forall(size_t k, k < i ==> s[k] == s[k]))
  {
    if (s[i] == 0)
      z++;
    i++;
  }
  return z;
}

size_t len(_array const char *s)
  _requires(_exists(size_t i, i < s._length && s[i] == 0))
  _requires(s._length <= PTRDIFF_MAX)
  _ensures(return < s._length && s[return] == 0)
{
  const char *a = s;
  for (; *s; s++)
    _invariant(s - a < a._length)
    _invariant(_forall(_specint k, 0 <= k && k < s - a ==> a[k] != 0));
  return s - a;
}

/* Pointers ordered by where they point, and a body local with the name a
   clause's quantifier binds: the clauses are read at the loop head. */
size_t count_back(_array uint8_t *s, size_t n)
  _requires(s._length == n && n <= 1000000)
  _ensures(return == n)
{
  uint8_t *p = s + n;
  size_t c = 0;
  while (p != s)
    _invariant(s <= p && p - s <= (_specint)n && (_specint)c + (p - s) == (_specint)n)
    _invariant(_forall(size_t k, k < s._length ==> s[k] == 0 || s[k] != 0))
  {
    size_t k = 1;
    p--;
    c += k;
  }
  return c;
}
