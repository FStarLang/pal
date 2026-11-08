#include "pal.h"
#include <stdint.h>

/* A local shadows the parameter `x`, so `var_x` is not the value the call
   passed everywhere in the body, and `_old(x)` is refused. */
int32_t shadow(int32_t x)
    _requires(0 <= x && x <= 100)
{
    int32_t r = x;
    {
        int32_t x = 5;
        r = r + x;
    }
    _assert(r == _old(x) + 5);
    return r;
}
