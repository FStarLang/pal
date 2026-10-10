#include "pal.h"
#include <stdint.h>
#include <stdbool.h>

// Non-tail `if`s. Pulse does not frame the `ensures` on a conditional, so the
// Palow translation has to restate the whole state at the join; these are the
// cases that exercise it.

// The branches disagree about `v`, so its value is forgotten at the join and
// what follows sees only that the storage is still there. `kept` is untouched
// by either branch, so the join keeps its value.
uint32_t branch_then_use(bool b)
{
    uint32_t kept = 7;
    uint32_t v = 0;
    if (b)
        _ensures(_live(kept) && _live(v) && _live(b))
    {
        v = 1;
    } else {
        v = 2;
    }
    return v + kept;
}

// Both branches leave `v` holding the same term, so the join keeps it.
uint32_t branch_agrees(bool b)
{
    uint32_t v = 3;
    if (b)
        _ensures(_live(v) && _live(b))
    {
        v = 4;
    } else {
        v = 4;
    }
    return v;
}

// A store through an out-parameter on both paths: the parameter is
// uninitialised on entry to the `if` and initialised on both arms, so the two
// arms agree about its state and the join can talk about it at all.
void store_on_both_paths(_out uint32_t *out, bool b)
{
    if (b) {
        *out = 10;
    } else {
        *out = 20;
    }
}
