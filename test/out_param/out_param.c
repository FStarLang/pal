#include "pal.h"
#include <stdbool.h>

void init_value(_out int *x)
    _ensures(*x == 42)
{
    *x = 42;
}

int call_init_value()
    _ensures(return == 42)
{
    int x;
    init_value(&x);
    return x;
}

void init_addressed(_out int *x, bool b)
    _ensures(*x == 42)
{
    if (b) {
        _assert(_live(x));
        *x = 42;
    } else {
        _assert(_live(x));
        *x = 42;
    }
}

void init_by_call_addressed(_out int *x, bool b)
    _ensures(*x == 42)
{
    if (b) {
        _assert(_live(x));
    }
    init_value(x);
}

void init_mixed_addressed(_out int *x, bool b)
    _ensures(*x == 42)
{
    if (b)
        _ensures(_inline_pulse(
            exists* (v: Int32.t).
                int32_t_pts_to $(x) 1.0R v **
                pure (Int32.v v == 42) **
                ptr_pts_to $&(x) 1.0R $(x)))
    {
        *x = 42;
    } else {
        init_value(x);
    }
}