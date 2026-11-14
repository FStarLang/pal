// An `if` whose `_ensures` states ownership is the whole state at its join,
// and what it does not mention is framed there. A local that neither the
// condition nor an arm writes still holds the value it had before the `if`,
// so the frame keeps that value, and what is known about it.

#include "pal.h"
#include <stdint.h>

// `x` is not mentioned, and not written: it is framed at its current value.
int32_t framed(_Bool c)
    _ensures(return == 5)
{
    int32_t x = 5;
    int32_t n = 0;
    _ghost_stmt(SwitchModel.start 0);
    if (c)
        _ensures(_live(n) && n <= 1 &&
                 (_slprop)_inline_pulse(SwitchModel.after 0))
    {
        _ghost_stmt(SwitchModel.step 0);
        n = 1;
    }
    else
    {
        _ghost_stmt(SwitchModel.step 0);
    }
    _ghost_stmt(SwitchModel.drop_after 0);
    return x;
}

// `x` is named, `$&(x)`, so its ownership is the author's to state; it is
// still not written, so `$(x)` in the same clause is its value before the
// `if`.
int32_t stated(_Bool c)
    _ensures(return == 5)
{
    int32_t x = 5;
    int32_t n = 0;
    _ghost_stmt(SwitchModel.start 0);
    if (c)
        _ensures(_live(n) && n <= 1 &&
                 (_slprop)_inline_pulse(
                     int32_t_pts_to $&(x) 1.0R $(x) **
                     pure (Int32.v $(x) == 5) ** SwitchModel.after 0))
    {
        _ghost_stmt(SwitchModel.step 0);
        n = 1;
    }
    else
    {
        _ghost_stmt(SwitchModel.step 0);
    }
    _ghost_stmt(SwitchModel.drop_after 0);
    return x;
}
