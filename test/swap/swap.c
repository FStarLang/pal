#include "pal.h"

void swap(int *x, int *y)
    _ensures(*y == _old(*x) && *x == _old(*y))
{
    int tmp = *y;
    *y = *x;
    *x = tmp;
}