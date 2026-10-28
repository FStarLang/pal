#include "pal.h"
#include <stdint.h>

struct cell {
    int *value;
};

struct holder {
    struct cell cell;
};

struct outer {
    struct holder holder;
};

int read_cell(const struct cell *cell)
    _ensures(return == *cell->value)
{
    return *cell->value;
}

int read_embedded(const struct holder *holder)
    _ensures(return == *holder->cell.value)
{
    return read_cell(&holder->cell);
}

int read_direct(const struct holder *holder)
    _ensures(return == *holder->cell.value)
{
    return *holder->cell.value;
}

void write_direct(struct holder *holder, int value)
    _ensures(*holder->cell.value == value)
{
    *holder->cell.value = value;
}

void write_cell(struct cell *cell, int value)
    _ensures(*cell->value == value)
{
    *cell->value = value;
}

int read_after_mutable_borrow(struct holder *holder, int value)
    _ensures(return == value)
{
    write_cell(&holder->cell, value);
    return read_direct(holder);
}

int read_after_nested_mutable_borrow(struct outer *outer, int value)
    _ensures(return == value)
{
    write_cell(&outer->holder.cell, value);
    return *outer->holder.cell.value;
}

int read_after_conditional_mutable_borrow(struct holder *holder, _Bool write)
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

int read_twice_embedded(const struct outer *outer)
    _ensures(return == *outer->holder.cell.value)
{
    return read_embedded(&outer->holder);
}

int read_after_conditional_borrow(const struct holder *holder, _Bool borrow)
    _ensures(return == *holder->cell.value)
{
    int value = 0;
    if (borrow)
        value = read_cell(&holder->cell);
    return read_direct(holder);
}

struct pair {
    struct cell left;
    struct cell right;
};

int read_pair(const struct cell *left, const struct cell *right)
{
    return *left->value;
}

int read_pair_value(const struct pair *pair)
{
    return *pair->left.value;
}

int read_after_pair_borrow(const struct pair *pair, _Bool borrow)
{
    int value = 0;
    if (borrow)
        value = read_pair(&pair->left, &pair->right);
    return read_pair_value(pair);
}

struct array_cell {
    _refine(this._length == 3) _array int *values;
};

struct array_holder {
    struct array_cell cell;
};

int read_third(const struct array_cell *cell)
{
    return cell->values[2];
}

int read_embedded_array(const struct array_holder *holder)
{
    return read_third(&holder->cell);
}

int read_direct_array(const struct array_holder *holder)
{
    return holder->cell.values[2];
}
