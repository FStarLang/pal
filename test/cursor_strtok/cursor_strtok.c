#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* The length of the longest prefix of `s` whose chars all occur in `c`. */
size_t spn(_array const char *s, _array const char *c)
  _requires(_exists(size_t i, i < s._length && s[i] == 0))
  _requires(_exists(size_t i, i < c._length && c[i] == 0))
  _requires(s._length <= PTRDIFF_MAX)
  _ensures(return < s._length)
  _ensures(_forall(size_t k, k < return ==> s[k] != 0
    && _exists(size_t j, j < c._length && c[j] == s[k]
      && _forall(size_t m, m < j ==> c[m] != 0))))
  _ensures(s[return] == 0 || _forall(size_t j, j < c._length
    && _forall(size_t m, m < j ==> c[m] != 0) ==> c[j] != s[return]));

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

/* musl's strtok_r, unchanged. The cursor starts at `s` if it is not null
   and at the incoming `*p` otherwise; in a contract `_old(*p)` is that start
   (`_cursor_from(s)`), and when `s` is not null `*p` need not hold anything
   on entry. The token skips `l0` chars of `sep` (`return - _old(*p)`), runs
   to the first char of `sep` or the terminator, a separator is overwritten
   by 0 and `*p` moves past it (`l` is where it was), and at the terminator
   `*p` becomes null with the array unchanged. Only separators left: null,
   and `*p` null. */
char *tok(_nullable _array char *restrict s, _array const char *restrict sep,
          _cursor_from(s) char **restrict p)
  _requires(*p != 0 ==> (*p)._length <= PTRDIFF_MAX
    && _exists(size_t i, i < (*p)._length && (*p)[i] == 0))
  _requires(_exists(size_t i, i < sep._length && sep[i] == 0))
  _ensures(_old(*p) == 0 ==> return == 0 && *p == 0)
  _ensures(_old(*p) != 0 && return == 0 ==> *p == 0
    && _forall(size_t k, k < _old(*p)._length ==> _old(*p)[k] == _old((*p)[k]))
    && _exists(size_t l0, l0 < _old(*p)._length && _old((*p)[l0]) == 0
      && _forall(size_t k, k < l0 ==> _old((*p)[k]) != 0
        && _exists(size_t j, j < sep._length && sep[j] == _old((*p)[k])
          && _forall(size_t m, m < j ==> sep[m] != 0)))))
  _ensures(return != 0 ==> _exists(size_t l0 = return - _old(*p),
    return == _old(*p) + l0 && _old((*p)[l0]) != 0
    && _forall(size_t k, k < l0 ==> _old((*p)[k]) != 0
      && _exists(size_t j, j < sep._length && sep[j] == _old((*p)[k])
        && _forall(size_t m, m < j ==> sep[m] != 0)))))
  _ensures(return != 0 && *p == 0 ==>
    _forall(size_t k, k < _old(*p)._length ==> _old(*p)[k] == _old((*p)[k]))
    && _exists(size_t l0 = return - _old(*p), _exists(size_t n,
      (_specint)l0 + n < _old(*p)._length && _old((*p)[(_specint)l0 + n]) == 0
      && _forall(size_t k, l0 <= k && k < (_specint)l0 + n ==> _old((*p)[k]) != 0
        && _forall(size_t j, j < sep._length
          && _forall(size_t m, m < j ==> sep[m] != 0) ==> sep[j] != _old((*p)[k]))))))
  _ensures(return != 0 && *p != 0 ==> _exists(size_t l0 = return - _old(*p),
    _exists(size_t l = *p - _old(*p) - 1, l0 < l && l < _old(*p)._length
      && _forall(size_t k, l0 <= k && k < l ==> _old((*p)[k]) != 0
        && _forall(size_t j, j < sep._length
          && _forall(size_t m, m < j ==> sep[m] != 0) ==> sep[j] != _old((*p)[k])))
      && _old(*p)[l] == 0
      && _exists(size_t j, j < sep._length && sep[j] == _old((*p)[l]) && sep[j] != 0)
      && _forall(size_t k, k < _old(*p)._length && k != l
        ==> _old(*p)[k] == _old((*p)[k])))))
{
	if (!s && !(s = *p)) return NULL;
	s += spn(s, sep);
	if (!*s) return *p = 0;
	*p = s + cspn(s, sep);
	if (**p) *(*p)++ = 0;
	else *p = 0;
	return s;
}
