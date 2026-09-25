#include "pal.h"
#include <stdint.h>

/* Labels and local variables have separate C identifier namespaces.
   Only the label spelling differs between these two cases. */
int32_t same_name(int32_t x)
    _ensures(return == 30)
{
    int32_t out = 0;
    if (x != 0)
        goto out;
    out = 42;
out: _ensures(_live(out) && _live(x))
    out = 30;
    return out;
}

int32_t distinct_name(int32_t x)
    _ensures(return == 30)
{
    int32_t out = 0;
    if (x != 0)
        goto done;
    out = 42;
done: _ensures(_live(out) && _live(x))
    out = 30;
    return out;
}
