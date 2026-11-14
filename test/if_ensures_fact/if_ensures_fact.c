// An `if` whose `_ensures` states a fact but no ownership.
//
// Pulse joins an `if` by itself, keeping what the arms own but not what they
// proved about it: each arm here stores a value it knows to be at most 8, and
// after Pulse's join the stored value is a fresh one about which nothing is
// known. The `_ensures` is the fact the code after the `if` needs, so it has
// to be the join, as one stating ownership already is.

#include "pal.h"
#include <stdint.h>

uint32_t min8(uint32_t a)
    _ensures(return <= 8)
{
    return a < 8 ? a : 8;
}

uint32_t pick(uint32_t k, uint32_t a, uint32_t b)
    _ensures(return <= 8)
{
    uint32_t m;
    if (k == 1)
        _ensures(_live(m) && m <= 8)
    {
        m = min8(a);
    }
    else
    {
        m = min8(b);
    }
    return m;
}

// The same through a `switch` with no fall-through, lowered to a chain of
// `if`s each carrying the `_ensures`.
uint32_t pick3(uint32_t k, uint32_t a, uint32_t b)
    _ensures(return <= 8)
{
    uint32_t m = 0;
    switch (k)
        _ensures(_live(k) && _live(m) && m <= 8)
    {
    case 1:
        m = min8(a);
        break;
    case 2:
        m = min8(b);
        break;
    default:
        m = 3;
        break;
    }
    return m;
}
