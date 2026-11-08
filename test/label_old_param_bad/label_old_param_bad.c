#include "pal.h"
#include <stdint.h>

/* After the loop, `n` is no longer what the call passed. */
int32_t walk(int32_t n)
    _requires(0 < n && n <= 100)
{
    int32_t steps = 0;
    while (n > 0)
        _invariant(_live(n) && _live(steps))
        _invariant(0 <= n && steps + n == _old(n))
    {
        n = n - 1;
        steps = steps + 1;
    }
    goto done;
done: _ensures(_live(n) && _live(steps) && n == _old(n))
    return steps;
}
