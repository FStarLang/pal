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

int ternary_requires_without_ensures(int x, int y, int z)
{
    _ternary_requires(_live(x));
    x = x > 0 ? y : z;
    return x;
}

int if_requires_without_ensures(int x)
{
    if (x > 0)
        _requires(_live(x))
    {
        x = x + 1;
    }
    return x;
}
