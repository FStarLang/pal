#include "pal.h"
#include <stdint.h>

/* A function whose return type carries a `_refine` promises it of the
   result, so a caller may rely on it. */

typedef _refine(this < 10) uint32_t small;

small f(void) { return 3; }

uint32_t g(void)
    _ensures(return < 10)
{
    small s = f();
    return s;
}
