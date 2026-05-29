#include <assert.h>
#include "pal.h"
#include <stdint.h>

/* C assert is translated so that we both 1) statically check the condition is
 * true and 2) that the program is correct whether we run the condition or not. */
int32_t checked_add(int32_t a, int32_t b)
    _requires(a >= 0 && a < 1000 && b >= 0 && b < 1000)
    _ensures(return == a + b)
{
    int32_t result = a + b;
    assert(result >= 0);
    return result;
}

void check_nonnull(const int *x) {
    _ghost_stmt(pts_to_not_null $(x));
    assert(x);
}