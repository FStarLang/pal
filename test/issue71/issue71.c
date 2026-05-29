#include "pal.h"
#include <stdint.h>

void incr1(int *x)
    _requires(*x + 1 < INT32_MAX)
{
    *x = *x + 1;
}

void incr2(int *x)
    _requires(*x + (_specint) 1 < INT32_MAX)
    _requires(*x + (int) 1 < INT32_MAX)
{
    *x = *x + 1;
}

void incr3(int *x)
    _requires(*x + (_specint) 1 < INT32_MAX)
{
    *x = *x + 1;
}