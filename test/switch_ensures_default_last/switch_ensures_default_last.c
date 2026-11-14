// A `switch` with an `_ensures` whose last case is the `default`, and which
// ends without a `break`: falling out of the last case leaves the `switch`,
// as a `break` would, so the cases are still one chain of choices.

#include "pal.h"
#include <stdint.h>

int default_last(uint32_t k)
{
    int r = 0;
    _ghost_stmt(SwitchModel.start 0);
    switch (k)
        _ensures(_live(k) && _live(r) && r >= 1 && (k == 1 ==> r == 2) &&
                 (_slprop)_inline_pulse(SwitchModel.after 0))
    {
    case 0:
        _ghost_stmt(SwitchModel.step 0);
        r = 1;
        break;
    case 1:
        _ghost_stmt(SwitchModel.step 0);
        r = 2;
        break;
    default:
        _ghost_stmt(SwitchModel.step 0);
        r = 3;
    }
    _ghost_stmt(SwitchModel.drop_after 0);
    return r;
}

