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
