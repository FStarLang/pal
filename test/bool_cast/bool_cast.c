#include "pal.h"
#include <stdbool.h>
#include <stdlib.h>
#include <stdint.h>

_pure bool cast_int_to_bool(int x)
    _ensures(return == (bool) x)
    _ensures(return == (x != 0))
{
    return x;
}

_pure int cast_bool_to_int(bool x)
    _ensures(return == (int) x)
    _ensures(x ==> return == 1)
    _ensures(!x ==> return == 0)
{
    return x;
}

_pure unsigned cast_bool_to_uint(bool x)
    _ensures(return == (unsigned) x)
    _ensures(x ==> return == 1)
    _ensures(!x ==> return == 0)
{
    return x;
}

_pure bool cast_unsigned_to_bool(unsigned x)
    _ensures(return == (bool) x)
    _ensures(return == (x != 0))
{
    return x;
}

_pure unsigned cast_bool_to_unsigned(bool x)
    _ensures(return == (unsigned) x)
    _ensures(x ==> return == 1)
    _ensures(!x ==> return == 0)
{
    return x;
}

_pure bool cast_size_to_bool(size_t x)
    _ensures(return == (bool) x)
    _ensures(return == (x != 0))
{
    return x;
}

_pure size_t cast_bool_to_sizet(bool x)
    _ensures(return == (size_t) x)
    _ensures(x ==> return == 1)
    _ensures(!x ==> return == 0)
{
    return x;
}

bool cast_pointer_to_bool(_plain int *x)
    _ensures(return == (bool) x)
    _ensures(return == (x != 0))
    _ensures(return == (x != NULL))
{
    return x;
}