// A `switch` whose cases never fall through into one another, with an
// `_ensures` that is not the state the `switch` was entered in.
//
// A case that cannot fall through is a choice, as an `if` is, and the
// `_ensures` is the join of all of them. Desugared into a test per case,
// guarded by flags for fall-through, the state between two tests is either
// the join (some earlier case ran) or the entry state (none did), and the
// `_ensures` cannot be both. So the cases have to be one chain of choices.
// They are here even though a case ends inside a block, and another leaves
// the function, so neither ends in a `break` of its own.

#include "pal.h"
#include <stdint.h>

int choose(uint32_t k)
{
    int r = 0;
    _ghost_stmt(SwitchModel.start 0);
    switch (k)
        _ensures(_live(k) && _live(r) && r >= 1 &&
                 (_slprop)_inline_pulse(SwitchModel.after 0))
    {
    case 0:
        {
            _ghost_stmt(SwitchModel.step 0);
            r = 1;
            break;
        }
    case 1:
    case 2:
        _ghost_stmt(SwitchModel.drop_before 0);
        return -1;
    default:
        _ghost_stmt(SwitchModel.step 0);
        r = 2;
        break;
    }
    _ghost_stmt(SwitchModel.drop_after 0);
    return r;
}

// The same after an early `return`, which makes the `switch` the tail of an
// arm whose join is already stated, as is every link of the chain.
int after_guard(uint32_t k)
{
    int r = 0;
    if (k > 9)
        return 0;
    _ghost_stmt(SwitchModel.start 0);
    switch (k)
        _ensures(_live(k) && _live(r) && r >= 1 &&
                 (_slprop)_inline_pulse(SwitchModel.after 0))
    {
    case 0:
        _ghost_stmt(SwitchModel.step 0);
        r = 1;
        break;
    case 1:
        {
            _ghost_stmt(SwitchModel.step 0);
            r = 2;
            break;
        }
    default:
        _ghost_stmt(SwitchModel.step 0);
        r = 3;
        break;
    }
    _ghost_stmt(SwitchModel.drop_after 0);
    return r;
}
