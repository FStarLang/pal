#include "pal.h"
#include <stdint.h>

void uninitialized_after_join(int *p, _Bool write)
{
    int x;
    if (write)
        _ensures((_slprop)_inline_pulse(
            exists* v. int32_t_pts_to $&(*p) 1.0R v))
    {
        *p = 1;
    }
    _assert(_live(x));
}
