#include "pal.h"

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