#include "refined.h"

_plain const char *call_choose(_plain const char *fallback)
    _ensures(return == fallback)
{
    return choose(1, fallback);
}

_plain const char *call_keep(_plain const char *fallback)
    _ensures(return == fallback)
{
    return keep(1, fallback);
}
