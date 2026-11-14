#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* The length of the longest prefix of `s` with no char from `c`. */
size_t cspn(_array const char *s, _array const char *c)
  _requires(_exists(size_t i, i < s._length && s[i] == 0))
  _requires(_exists(size_t i, i < c._length && c[i] == 0))
  _requires(s._length <= PTRDIFF_MAX)
  _ensures(return < s._length)
  _ensures(_forall(size_t k, k < return ==> s[k] != 0
    && _forall(size_t j, j < c._length
      && _forall(size_t m, m < j ==> c[m] != 0) ==> c[j] != s[k])))
  _ensures(s[return] == 0 || _exists(size_t j, j < c._length && c[j] == s[return]
    && _forall(size_t m, m < j ==> c[m] != 0)));

/* musl's strsep: `*str` is null or points into a terminated array, which
   the function owns for the call. The token at `*str` ends at the first
   char of `sep` or the terminator; a separator is overwritten by 0 and
   `*str` moves past it, a terminator leaves `*str` null. */
char *sep(_cursor char **str, _array const char *sep)
  _requires(*str != 0 ==> (*str)._length <= PTRDIFF_MAX
    && _exists(size_t i, i < (*str)._length && (*str)[i] == 0))
  _requires(_exists(size_t i, i < sep._length && sep[i] == 0))
  _ensures(return == _old(*str))
  _ensures(_old(*str) == 0 ==> *str == 0)
  _ensures(_old(*str) != 0 ==> _exists(size_t l, l < _old(*str)._length
    && _forall(size_t k, k < l ==> _old((*str)[k]) != 0
      && _forall(size_t j, j < sep._length
        && _forall(size_t m, m < j ==> sep[m] != 0) ==> sep[j] != _old((*str)[k])))
    && _forall(size_t k, k < _old(*str)._length && k != l
      ==> _old(*str)[k] == _old((*str)[k]))
    && _old(*str)[l] == 0
    && (_old((*str)[l]) == 0 ==> *str == 0)
    && (_old((*str)[l]) != 0 ==> *str != 0 && *str - _old(*str) == l + 1
      && _exists(size_t j, j < sep._length && sep[j] == _old((*str)[l])))))
{
  char *s = *str, *end;
  if (!s) return NULL;
  end = s + cspn(s, sep);
  if (*end) *end++ = 0;
  else end = 0;
  *str = end;
  return s;
}

/* A `_nullable _array` parameter's contents, under a null test. */
char first(_nullable _array const char *a)
  _requires(a != 0 ==> a._length > 0)
  _ensures(a != 0 ==> return == a[0])
{
  const char *s = a;
  if (!s) return 0;
  return s[0];
}
