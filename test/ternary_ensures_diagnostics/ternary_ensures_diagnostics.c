#include "pal.h"

int no_ternary(int x)
{
    _ternary_ensures(_live(x));
    x = x + 1;
    return x;
}

int nested_ternary(int x, int y, int z)
{
    _ternary_ensures(_live(x));
    x = x > 0 ? (y > 0 ? y : z) : z;
    return x;
}
