#include "pal.h"
#include <stdint.h>

/* The `_ensures` is false on the path through the arm that may leave: `b` may
   be 1. It is checked at the join, not dropped because the arm has a `goto`;
   nothing after the `if` needs it. */
int32_t joined(int32_t a, int32_t b, uint32_t n)
{
    int32_t status = a;
    uint32_t i = 0;
    if (b != 0)
        _ensures(status > 1)
    {
        status = b;
        if (status < 0)
            goto out;
    } else {
        status = 2;
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
