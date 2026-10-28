#include "pal.h"
#include <stdbool.h>

void init_value(_out int *x)
    _ensures(*x == 42)
{
    *x = 42;
}

int call_init_value()
    _ensures(return == 42)
{
    int x;
    init_value(&x);
    return x;
}

void init_addressed(_out int *x, bool b)
    _ensures(*x == 42)
{
    if (b) {
        _assert(_live(x));
        *x = 42;
    } else {
        _assert(_live(x));
        *x = 42;
    }
}

void init_by_call_addressed(_out int *x, bool b)
    _ensures(*x == 42)
{
    if (b) {
        _assert(_live(x));
    }
    init_value(x);
}