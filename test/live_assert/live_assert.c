#include "pal.h"

int local_value(int x)
    _ensures(return == x)
{
    int y = x;
    _assert(_live(y));
    return y;
}

int pointee(int *p)
    _ensures(return == *p)
{
    _assert(_live(p));
    _assert(_live(*p));
    return *p;
}

int cleanup(int x)
    _ensures(return == x)
{
    int y = x;
    if (x < 0)
        goto done;
done:
    _ensures(_live(x) && _live(y) && y == x)
    return y;
}

int spliced_cleanup(int x)
    _ensures(return == x)
{
    int y = x;
    goto done;
done:
    _ensures(_live(y) &&
        (_slprop)_inline_pulse(pure ($(y) == $(x))))
    return y;
}

int spliced_parameter(int x)
    _ensures(return == x)
{
    int y = x;
    if (x < 0)
        goto done;
done:
    _ensures(_live(y) && y == x &&
        (_slprop)_inline_pulse(int32_t_pts_to $&(x) 1.0R $(x)))
    return y;
}

int ghost_parameter(int x)
    _ensures(return == x)
{
    if (x < 0) {
        _ghost_stmt(int32_t_pts_to_not_null $&(x));
    }
    return x;
}

int loop_cleanup(int n)
    _requires(0 <= n && n <= 100)
    _ensures(return == n)
{
    int i = 0;
    while (i < n)
        _invariant(0 <= i && i <= n)
        _ensures(_live(i) && i == n)
    {
        i++;
    }
    return i;
}
