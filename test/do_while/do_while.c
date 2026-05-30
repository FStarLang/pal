#include "pal.h"
#include <stdint.h>

/* do-while with user-named flag variable for first-iteration invariant */
uint32_t simple_do(uint32_t n)
    _requires(n >= 1 && n <= 100)
{
    uint32_t i = 0;
    do
        _do_while_first(first)
        _invariant(_live(i) && _live(n) && _live(first))
        _invariant(first ==> (_specint) i < n)
        _invariant((_specint) i <= n)
    {
        i = i + 1;
    } while (i < n);
    return i;
}

/* do-while(0): execute body exactly once (no flag needed) */
uint32_t run_once(uint32_t x)
    _requires(x <= 100)
{
    uint32_t r = 0;
    do
        _invariant(_live(r))
    {
        r = x;
    } while (0);
    return r;
}

/* do-while with break: search for a threshold */
uint32_t find_limit(uint32_t n, uint32_t limit)
    _requires(n >= 1 && n <= 100 && limit <= 100)
{
    uint32_t i = 0;
    do
        _do_while_first(first)
        _invariant(_live(i) && _live(n) && _live(limit) && _live(first))
        _invariant(first ==> (_specint) i < n)
        _invariant((_specint) i <= n)
        _ensures((_specint) i <= n)
    {
        if (i == limit) {
            break;
        }
        i = i + 1;
    } while (i < n);
    return i;
}

/* do-while with continue: skip even iterations */
uint32_t count_odd(uint32_t n)
    _requires(n >= 1 && n <= 100)
{
    uint32_t i = 0;
    uint32_t count = 0;
    do
        _do_while_first(first)
        _invariant(_live(i) && _live(count) && _live(n) && _live(first))
        _invariant(first ==> (_specint) i < n)
        _invariant((_specint) i <= n)
        _invariant((_specint) count <= i)
    {
        i = i + 1;
        if (i % 2 == 0) {
            continue;
        }
        count = count + 1;
    } while (i < n);
    return count;
}
