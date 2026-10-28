#include "pal.h"
#include <stdint.h>

int delayed_scalar(int *p, _Bool write)
    _ensures(return == *p)
{
    int result;
    if (write)
        _ensures((_slprop)_inline_pulse(
            exists* v. int32_t_pts_to $&(*p) 1.0R v))
    {
        *p = 1;
    }
    result = *p;
    return result;
}

union result {
    int value;
    unsigned bits;
};

int delayed_union(int *p, _Bool write)
    _ensures(return == *p)
{
    union result result;
    if (write)
        _ensures((_slprop)_inline_pulse(
            exists* v. int32_t_pts_to $&(*p) 1.0R v))
    {
        *p = 2;
    }
    result.value = *p;
    return result.value;
}
