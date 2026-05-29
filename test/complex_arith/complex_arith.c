#include "pal.h"
#include <stdint.h>

_let(bool int_fits(_specint x), INT32_MIN <= x && x <= INT32_MAX)

int triple(int x)
    _requires(int_fits((_specint) x * 3))
    _ensures(return == x * 3)
{
    return x * 3;
}

int square(int x)
    _requires(int_fits((_specint) x * x))
    _ensures(return == x * x)
{
    return x * x;
}

int double_value(int x)
    _requires(int_fits((_specint) x * 2))
    _ensures(return == x * 2)
{
    return x * 2;
}

int sum(int x, int y)
    _requires(int_fits((_specint) x + y))
    _ensures(return == x + y)
{
    return x + y;
}
