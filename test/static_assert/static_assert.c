#include "pal.h"
#include <stdint.h>

/* _Static_assert is a compile-time check enforced by Clang.
   pal should silently skip it (no Pulse representation needed). */
_Static_assert(sizeof(int32_t) == 4, "int32_t must be 4 bytes");
_Static_assert(1, "trivially true");

int32_t identity(int32_t x)
    _requires(x >= 0 && x < 100)
    _ensures(return == x)
{
    return x;
}
