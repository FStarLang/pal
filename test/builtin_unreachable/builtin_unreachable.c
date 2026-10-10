// `__builtin_unreachable()` is how a `noreturn` abort is spelled to the C
// compiler. A switch whose default arm can only be reached by a caller that
// broke a precondition ends with one, and without it the compiler reports the
// fall-through as a use of an uninitialized variable.
//
// PAL models it as the claim it is: `unreachable ()`, discharged rather than
// assumed. The preconditions below are what make the dead arms dead; dropping
// either makes this file fail to verify.
#include "pal.h"
#include <stdint.h>

uint32_t
pick(uint32_t version) _requires(version == 1 || version == 2)
{
    uint32_t result = 0;

    switch (version)
    {
    case 1:
        result = 10;
        break;
    case 2:
        result = 20;
        break;
    default:
        __builtin_unreachable();
    }

    return result;
}

// The same shape without a switch: a tail the caller's precondition rules out.
uint32_t
halve(uint32_t n) _requires(n % 2 == 0)
{
    if (n % 2 != 0)
    {
        __builtin_unreachable();
    }

    return n / 2;
}

// The shape a version dispatcher has, and the reason the builtin is needed in
// the first place: two live arms, and a default arm that aborts and jumps to
// the function's single exit. That arm ends in a `goto` rather than a `break`,
// and the abort is wrapped in the `do { ... } while (0)` that every
// fatal-error macro uses to make itself a single statement -- so the switch
// has no fall-through even though not every arm ends in `break`, and the
// abort's claim has to survive the wrapper.
int32_t
dispatch(uint32_t version) _requires(version == 1 || version == 2)
    _ensures(return == 10 || return == 20)
{
    int32_t result;

    switch (version)
        _ensures(_live(version) && _live(result))
        _ensures(result == 10 || result == 20)
    {
    case 1:
        result = 10;
        break;
    case 2:
        result = 20;
        break;
    default:
        do
        {
            _assert(0);
            __builtin_unreachable();
        } while (0);
        goto Finally;
    }

Finally:
    _ensures(_live(version) && _live(result) && (result == 10 || result == 20))
    return result;
}

// The same dispatcher with the `goto` left off: the default arm's last
// statement is the abort itself, wrapped in the usual `do { ... } while (0)`
// and guarded by an `if` whose condition folds to true, which is what a fatal
// macro of the form `_assert(e); if (!(e)) __builtin_unreachable();` expands to
// when `e` is literally false.
//
// Nothing falls out of that arm either, and PAL has to see that: an arm it
// thinks falls through forces the general switch encoding, whose compound
// branch guard no arm can reason under.
int32_t
dispatch_abort_no_jump(uint32_t version) _requires(version == 2)
    _ensures(return == 20)
{
    int32_t result;

    switch (version)
        _ensures(_live(version) && _live(result))
        _ensures(result == 20)
    {
    case 2:
        result = 20;
        break;
    default:
        do
        {
            _assert(0);
            if (!0)
            {
                __builtin_unreachable();
            }
        } while (0);
    }

    return result;
}
