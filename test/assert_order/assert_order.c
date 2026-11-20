#include "pal.h"
#include <assert.h>
#include <stdint.h>

/* assert() must be translated even when assert.h is included after pal.h. */
int32_t checked_add2(int32_t a, int32_t b)
    _requires(a >= 0 && a < 1000 && b >= 0 && b < 1000)
    _ensures(return == a + b)
{
    int32_t result = a + b;
    assert(result >= 0);
    return result;
}
