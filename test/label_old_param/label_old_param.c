#include "pal.h"
#include <stdint.h>

/* `_old(p)` for a parameter `p` inside a body: in a label's `_ensures` and in
   `_assert`, it names the value the call passed, also after `p` is assigned. */

typedef struct { uint32_t n; } box;

int32_t keep_ptr(box *b, uint32_t k)
    _requires(_live(*b))
    _ensures(_live(*b))
{
    int32_t err = 0;
    if (k == 0)
        goto out;
    b->n = k;
    err = 1;
out: _ensures(b == _old(b) && k == _old(k) && _live(*b) && _live(err))
    return err;
}

int32_t walk(int32_t n)
    _requires(0 <= n && n <= 100)
    _ensures(return == _old(n))
{
    int32_t steps = 0;
    while (n > 0)
        _invariant(_live(n) && _live(steps))
        _invariant(0 <= n && steps + n == _old(n))
    {
        n = n - 1;
        steps = steps + 1;
    }
    _assert(n == 0 && steps == _old(n));
    if (steps == 0)
        goto done;
    _assert(steps > 0 && n < _old(n));
done: _ensures(_live(n) && _live(steps) && steps == _old(n) && n == 0)
    return steps;
}

void use(box *b, int32_t m)
    _requires(_live(*b) && 0 <= m && m <= 100)
    _ensures(_live(*b))
{
    keep_ptr(b, 3);
    int32_t r = walk(m);
    _assert(r == m);
}
