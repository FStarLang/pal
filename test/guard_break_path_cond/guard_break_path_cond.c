#include "pal.h"
#include <stdint.h>
#include <stdbool.h>

/* After `if (c) break;` the rest of the body runs only when c is false. */
bool is_done(uint32_t i, uint32_t lim)
    _ensures(return == (i >= lim));

uint32_t guard_break(uint32_t n, uint32_t lim)
{
    uint32_t i = 0;
    while (i < n)
        _invariant(_live(i))
        _invariant(i <= n)
    {
        if (is_done(i, lim))
        {
            break;
        }
        _assert(i < lim);
        i = i + 1;
    }
    return i;
}

/* The same with a `continue`, and a guard nested in a branch. */
uint32_t guard_continue(uint32_t n, uint32_t lim)
{
    uint32_t i = 0;
    uint32_t s = 0;
    while (i < n)
        _invariant(_live(i) && _live(s))
        _invariant(i <= n)
    {
        i = i + 1;
        if (n > 5)
        {
            if (is_done(i, lim))
            {
                continue;
            }
            _assert(i < lim);
        }
        s = i;
    }
    return s;
}
