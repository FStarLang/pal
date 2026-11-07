#include "pal.h"
#include <stdint.h>

struct cell {
    int *value;
};

struct holder {
    _plain struct cell cell;
};

int read_cell(const struct cell *cell)
{
    return *cell->value;
}

int read_unowned(const struct holder *holder)
{
    return read_cell(&holder->cell);
}
