#include "pal.h"
#include <stdint.h>

/* As switch_ensures_exit, but the case that reaches the end of the switch
   does not establish its `_ensures`: the clause is still checked there. */
int32_t pick(int32_t version, int32_t value)
    _requires(version == 2 && value >= 0)
    _ensures(return >= 0)
{
    int32_t result = -1;
    switch (version)
        _ensures(_live(result) && result > 0)
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
