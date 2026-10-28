#include "pal.h"
#include <stdint.h>

void initialized_on_one_path(int *p, _Bool write)
{
    int x;
    if (write)
        _ensures((_slprop)_inline_pulse(
            exists* v. int32_t_pts_to $&(*p) 1.0R v))
    {
        x = 1;
        *p = x;
    }
    _assert(_live(x));
}
