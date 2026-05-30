#include "pal.h"

int read_val(const int *x)
    _ensures(return == *x)
{
    return *x;
}

int call_read_val() {
    int x = 67;
    int y = read_val(&x);
    _assert(y == x && x == 67);
    return y;
}