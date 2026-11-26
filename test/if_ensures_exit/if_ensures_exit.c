#include "pal.h"
#include <stdint.h>

/* An `_ensures` on an `if` one of whose arms leaves by `goto`. The clause is
   the join of the arms that fall through, so it is checked there, and the
   loop after the `if` -- which needs it -- is translated once rather than
   once per arm. */
int32_t joined(int32_t a, int32_t b, uint32_t n)
{
    int32_t status = a;
    uint32_t i = 0;
    if (status < 0)
        goto out;
    if (b != 0)
        _ensures(status >= 0)
    {
        status = b;
        if (status < 0)
            goto out;
    }
    while (i < n)
        _invariant(_live(i) && _live(status) && status >= 0)
    {
        i++;
    }
    status = 0;
out: _ensures(_live(status) && _live(i))
    return status;
}

/* The same with a `return` in an arm, and the join speaking for both arms. */
int32_t returned(int32_t a, uint32_t n)
    _ensures(return >= -1)
{
    int32_t status = a;
    uint32_t i = 0;
    if (a > 100)
        _ensures(status >= 0 && status <= 100)
    {
        return -1;
    } else {
        if (status < 0)
            status = 0;
    }
    while (i < n)
        _invariant(_live(i) && _live(status) && status >= 0 && status <= 100)
    {
        i++;
    }
    return status;
}
