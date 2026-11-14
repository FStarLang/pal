// A parameter the function never reassigns, framed across an `if` and a loop.
//
// The parameter has a slot (a clause names it with `_live`), and a frame
// states what every slot holds. A fresh binder for it is equal to the
// parameter only as a pure fact, which slprop matching does not consult, so
// the token the contract states at the parameter stopped matching after the
// join. A parameter nothing rebinds still holds what the call passed in, and
// the frame says so.

#include "pal.h"
#include <stdint.h>

int joined(int *p, _Bool c)
    _requires((_slprop)_inline_pulse(TokModel.tok $(p)))
    _ensures((_slprop)_inline_pulse(TokModel.tok $(p)))
{
    int n = 0;
    if (c)
        _ensures(_live(p) && _live(c) && _live(n) && n <= 1 &&
                 (_slprop)_inline_pulse(TokModel.tok $(p)))
    {
        n = 1;
    }
    return n;
}

int looped(int *p, uint32_t k)
    _requires((_slprop)_inline_pulse(TokModel.tok $(p)))
    _ensures((_slprop)_inline_pulse(TokModel.tok $(p)))
{
    uint32_t i = 0;
    while (i < k)
        _invariant(_live(p) && _live(i) && _live(k) && i <= k)
        _invariant((_slprop)_inline_pulse(TokModel.tok $(p)))
    {
        if (i == 7)
            return 1;
        i = i + 1;
    }
    return 0;
}
