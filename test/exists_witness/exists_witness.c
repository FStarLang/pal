#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* A precondition that bounds a search: somewhere below `n` the search can
   stop, either because `n` runs out or because `l` ends. */
int cmpn(_array const char *l, size_t n)
  _requires(n == 0 || _exists(size_t i, i < n && i < l._length && (i == n - 1 || l[i] == 0)));

/* Calling it at every position of `h` needs a different witness depending on
   where `h`'s terminator lies; the assertion names both. */
int scan(_array const char *h, size_t n)
  _requires(_exists(size_t t, t < h._length && h[t] == 0))
  _requires(h._length <= PTRDIFF_MAX)
{
  int r = 0;
  for (; *h; h++)
    _invariant(h - _old(h) < _old(h)._length && _forall(_specint j, 0 <= j && j < h - _old(h) ==> _old(h)[j] != 0))
  {
    _assert(_forall(size_t t, t < _old(h)._length && _old(h)[t] == 0 ==> n == 0
       || ((_specint)t - (h - _old(h)) < (_specint)n - 1
          ==> _exists(size_t i = t - (h - _old(h)), i < n && i < h._length && (i == n - 1 || h[i] == 0)))
       && ((_specint)t - (h - _old(h)) >= (_specint)n - 1
          ==> _exists(size_t i = n - 1, i < n && i < h._length && (i == n - 1 || h[i] == 0)))));
    r = cmpn(h, n);
  }
  return r;
}

/* A witness in a contract, of each kind of bound variable. */
size_t third(_array const int32_t *a)
  _requires(a._length > 3)
  _ensures(_exists(size_t i = 2, i < a._length && return == i))
  _ensures(_exists(uint8_t b = 2, return == b))
  _ensures(_exists(int8_t c = -1, (_specint)return + c == 1))
  _ensures(_exists(_specint k = (_specint)return * 2, k == 4))
{
  return 2;
}

/* A plain equality conjunct pins the witness as well. */
void pinned(size_t n)
  _requires(n < 100)
{
  _assert(_exists(size_t m, m == n + 1 && n < m));
}
