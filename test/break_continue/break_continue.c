#include "pal.h"
#include <stdint.h>

/* Count up to n, stopping early at a given limit. */
uint32_t count_to_limit(uint32_t n, uint32_t limit)
{
    uint32_t i = 0;
    while (i < n)
        _invariant(_live(i))
        _invariant(i <= n)
        _ensures(i <= n)
    {
        if (i == limit) {
            break;
        }
        i = i + 1;
    }
    return i;
}

/* Sum only even numbers in [0, n) by skipping odds. */
uint32_t sum_evens(uint32_t n)
    _requires(n <= 10000)
{
    uint32_t i = 0;
    uint32_t s = 0;
    while (i < n)
        _invariant(_live(i) && _live(s))
        _invariant(i <= n)
        _invariant(s <= 10000 * i)
    {
        i = i + 1;
        if (i == 1) {
            continue;
        }
        s = s + i;
    }
    return s;
}
