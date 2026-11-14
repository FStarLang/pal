// An `if` whose `_ensures` states a slot's ownership itself, and does not read
// the slot's value, says nothing about the slot holding a value: the slot may
// be uninitialized there, or its ownership folded into a predicate. The join
// takes the author's words for it rather than asserting the slot initialized.

#include "pal.h"
#include <stdint.h>

struct pair {
    uint32_t first;
    uint32_t second;
};

// `x` was initialized, then given up: the clause states it uninitialized.
uint32_t stated_uninit(_Bool c)
    _ensures(return == 7)
{
    uint32_t x = 5;
    uint32_t n = 0;
    _ghost_stmt(uint32_t_forget $&(x));
    if (c)
        _ensures(_live(n) && n <= 1 &&
                 (_slprop)_inline_pulse(uint32_t_pts_to_uninit $&(x)))
    {
        n = 1;
    }
    else
    {
    }
    _assert((_slprop)_inline_pulse(uint32_t_pts_to_uninit $&(x)));
    x = 7;
    return x;
}

// `*p` is folded away; the clause names the predicate at `$&(*p)`.
void stated_hidden(_out struct pair *p, _Bool c)
{
    uint32_t n = 0;
    p->first = 1;
    p->second = 2;
    _ghost_stmt(Hidden.hide_it (exists* v. Struct_pair.struct_pair_pts_to $&(*p) 1.0R v));
    if (c)
        _ensures(_live(n) && n <= 1 &&
                 (_slprop)_inline_pulse(
                     Hidden.hide (exists* v. Struct_pair.struct_pair_pts_to $&(*p) 1.0R v)))
    {
        n = 1;
    }
    else
    {
    }
    _ghost_stmt(Hidden.show_it (exists* v. Struct_pair.struct_pair_pts_to $&(*p) 1.0R v));
}
