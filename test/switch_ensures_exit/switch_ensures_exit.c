#include "pal.h"
#include <stdint.h>

/* A switch whose first case leaves it by `goto`. The switch's `_ensures` is
   the join after the switch: it holds once a case has run and reached the
   end, not before any case has matched, which is the state in which the
   first case's lowered `if` is skipped. */
int32_t pick(int32_t version, int32_t value)
    _requires(version == 2 && value >= 0)
    _ensures(return >= 0)
{
    int32_t result = -1;
    switch (version)
        _ensures(_live(result) && result >= 0)
    {
    case 1:
        result = -2;
        goto out;
    case 2:
        result = value;
        break;
    }
out: _ensures(_live(result))
    return result;
}
