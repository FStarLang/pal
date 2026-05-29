#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

/* Mimic the CXPLAT_DBG_ASSERT pattern from msquic: in non-debug builds
   the macro expands to ((void)0), a standard C no-op. */
#define DBG_ASSERT(exp) ((void)0)

int32_t identity(int32_t x)
    _requires(x >= 0 && x < 100)
    _ensures(return == x)
{
    DBG_ASSERT(x >= 0);
    ((void)0);
    return x;
}

void void_cast_doesnt_drop_side_effects() {
    int x = 0;
    (void) x++;
    _assert(x == 1);
}