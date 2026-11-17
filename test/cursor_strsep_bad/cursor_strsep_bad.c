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

/* Clears the char after the token's end too: when the token ends at the
   terminator, that is past the array. */
void sep_bad(_cursor char **str, _array const char *sep)
  _requires(*str != 0 ==> (*str)._length <= PTRDIFF_MAX
    && _exists(size_t i, i < (*str)._length && (*str)[i] == 0))
  _requires(_exists(size_t i, i < sep._length && sep[i] == 0))
{
  char *s = *str, *end;
  if (!s) return;
  end = s + cspn(s, sep);
  *(end + 1) = 0;
}
