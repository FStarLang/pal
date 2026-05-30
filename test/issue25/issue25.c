#include "pal.h"

int test(int Arg)
    _ensures(return == Arg)
{ return Arg; }