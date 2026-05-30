#include "pal.h"
#include <stdbool.h>

int test_implies(bool a, bool b)
    _requires(a ==> b)
    _ensures(a ==> b)
    _ensures(!a || b)
    _ensures(_forall(int x, x == x))
{
    return 0;
}
