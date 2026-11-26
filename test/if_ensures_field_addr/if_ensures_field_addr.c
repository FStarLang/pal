#include "pal.h"
#include <stdint.h>

struct pair {
    uint64_t a;
    uint64_t b;
};

void set(uint64_t *x, uint64_t v)
    _requires(_live(*x))
    _ensures(_live(*x) && *x == v)
{
    *x = v;
}

/* An `_ensures` on an `if` that states ownership of a field of a local struct
   by the field's address, `$&(p.a)`, with an arm that leaves by `goto`. The
   clause is the join of the arms that fall through, so the address has to be
   the one the body uses for the field. */
int32_t field_join(int32_t a)
{
    int32_t status = a;
    struct pair p = { 0, 0 };
    _ghost_stmt(Struct_pair.struct_pair_scatter $&(p));
    _assert((_slprop)_inline_pulse(uint64_t_pts_to $&(p.a) 1.0R 0UL));
    set(&p.a, 1);
    if (status < 0)
        goto out;
    if (a != 7)
        _ensures(_inline_pulse(
            (exists* (v: UInt64.t). uint64_t_pts_to $&(p.a) 1.0R v) **
            uint64_t_pts_to $&(p.b) 1.0R 0UL **
            Struct_pair.struct_pair_padding $&(p) 1.0R))
    {
        set(&p.a, 2);
        if (a > 100)
            goto out;
    }
    set(&p.a, 3);
    status = 0;
out:
    _ghost_stmt(Struct_pair.struct_pair_gather $&(p));
    return status;
}
