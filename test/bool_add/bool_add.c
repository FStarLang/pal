#include "pal.h"
#include <stdbool.h>

int foo(bool a, bool b)
    _ensures(a == false && b == false ==> return == 0)
    _ensures(a == true && b == false || a == false && b == true ==> return == 1)
    _ensures(a == true && b == true ==> return == 2)
    _ensures(return == (_specint) a + b)
{
    return a + b;
}