#include "pal.h"
#include <stdint.h>

void nothing()
{
}

int answer()
    _ensures(return == 67)
{
    return 67;
}

int call_in_return()
    _ensures(return == 67)
{
    return answer();
}

int call_in_init()
    _ensures(return == 67)
{
    int x = answer();
    return x;
}

void call_void_stmt()
{
    nothing();
}

void discard_result()
{
    answer();
}

int call_in_cond()
    _ensures(return == 1)
{
    if (answer() == 67) {
        return 1;
    }
    return 0;
}
