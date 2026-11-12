#include "pal.h"
#include <stddef.h>

typedef struct { int a; } S;

/* An out-pointer cell whose final value the contract states, beside an
 * ownership clause about something else. The `_slprop` clause does not name
 * `out`, so it must not take the cell's ownership away from the caller: the
 * cell, and the binder `*out == s` speaks of, are still the mode's. */
void init(_plain S* s, _out S** out)
    _ensures(_inline_pulse(emp))
    _ensures(*out == s);

int use(_plain S* s)
    _ensures(return == 1)
{
    S* r = NULL;
    init(s, &r);
    return r == s ? 1 : 0;
}
