// An `if` whose `_ensures` states ownership alongside other conjuncts.
//
// Pulse does not frame an `if`'s annotation, and cannot always infer the
// join of two arms that leave the same ownership in different shapes, so an
// `_ensures` that states ownership is the join. That holds whether the
// ownership is the whole clause or one conjunct of it: `_live(..) && slprop`
// is just as much the author's statement of the state after the `if`.

#include "pal.h"
#include <stdint.h>

struct cell {
    int *value;
};

struct holder {
    struct cell cell;
};

int read_direct(const struct holder *holder)
    _ensures(return == *holder->cell.value)
{
    return *holder->cell.value;
}

void write_cell(struct cell *cell, int value)
    _ensures(*cell->value == value)
{
    *cell->value = value;
}

// The ownership alone (as in embedded_struct_own).
int bare(struct holder *holder, _Bool write)
{
    if (write)
        _ensures((_slprop)_inline_pulse(
            exists* (v: Struct_holder.struct_holder)
                    (s: Struct_holder.struct_holder_own_spec).
                Struct_holder.struct_holder_pts_to $&(*holder) 1.0R v **
                Struct_holder.struct_holder_own v 1.0R s))
    {
        write_cell(&holder->cell, 1);
    }
    return read_direct(holder);
}

// The same ownership as one conjunct among others.
int conjoined(struct holder *holder, _Bool write)
{
    int n = 0;
    if (write)
        _ensures(_live(write) && n <= 1 &&
                 (_slprop)_inline_pulse(
            exists* (v: Struct_holder.struct_holder)
                    (s: Struct_holder.struct_holder_own_spec).
                Struct_holder.struct_holder_pts_to $&(*holder) 1.0R v **
                Struct_holder.struct_holder_own v 1.0R s))
    {
        write_cell(&holder->cell, 1);
        n = 1;
    }
    int r = read_direct(holder);
    return n == 1 ? r : 0;
}
