#include "pal.h"
#include <stdint.h>

#include <stddef.h>

/* An `if` one of whose arms always leaves -- by `return`, `break` or
   `continue` -- inside a loop: the statements after it run only when that arm
   is not taken, and they know the test came out the other way. */

int first_zero(_array const char *s, int n, int c)
    _requires(0 <= n && n <= s._length)
    _ensures(return >= 0)
{
    for (int i = 0; i < n; i++)
        _invariant(0 <= i && i <= n)
    {
        if (!s[i] || s[i] == c) {
            return i;
        }
        _assert(s[i] != 0 && s[i] != c);
        int t = s[i];
        _assert(t != 0);
    }
    return n;
}

int count_nonzero(_array const char *s, int n)
    _requires(0 <= n && n <= s._length)
    _ensures(return >= 0)
{
    int k = 0;
    for (int i = 0; i < n; i++)
        _invariant(0 <= i && i <= n && 0 <= k && k <= i)
    {
        if (s[i] == 0)
            continue;
        _assert(s[i] != 0);
        k++;
    }
    return k;
}

void until_zero(_array const char *s, int n)
    _requires(0 <= n && n <= s._length)
{
    for (int i = 0; i < n; i++)
        _invariant(0 <= i && i <= n)
    {
        if (s[i] != 0) {
        } else {
            break;
        }
        _assert(s[i] != 0);
    }
}

/* musl's strchrnul loop shape, on a walked pointer. */
const char *chrnul(_array const char *s, int c)
    _requires(_exists(size_t i, i < s._length && s[i] == 0))
    _requires(s._length <= 1000000)
    _ensures(_exists(size_t i, i < s._length && return == s + i
        && (s[i] == 0 || s[i] == c)))
{
    for (;; s++)
        _invariant(_exists(size_t i, s - _old(s) <= i && i < _old(s)._length && _old(s)[i] == 0))
    {
        if (!*s || *s == c) {
            _assert(_exists(size_t i, i == s - _old(s) && i < _old(s)._length
                && (_old(s)[i] == 0 || _old(s)[i] == c)));
            return s;
        }
        _assert(_forall(size_t i, i == s - _old(s) ==> _old(s)[i] != 0));
    }
    return s;
}
