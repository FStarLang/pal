#include "pal.h"
#include <stdint.h>

/* By default PAL emits every function as `divergent fn`. The `_total`
 * annotation opts a loop-free (trivially terminating) function back into
 * termination checking, so it is emitted as a plain `fn`. */
_total
uint32_t add_one(uint32_t x)
    _requires(x < 100)
    _ensures(return == x + 1)
{
    return x + 1;
}

/* A function without `_total` stays divergent by default. */
uint32_t add_two(uint32_t x)
    _requires(x < 100)
    _ensures(return == x + 2)
{
    return x + 2;
}
