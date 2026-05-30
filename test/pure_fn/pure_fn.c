#include "pal.h"
#include <stdbool.h>

_pure bool pure_not(bool x)
        _ensures(return == !x)
{
    if (x) {
        return false;
    } else {
        return true;
    }
}

_pure bool pure_and(bool x, bool y) {
    if (x) {
        return y;
    } else {
        return false;
    }
}

_pure bool pure_or(bool x, bool y) {
    if (x) {
        return true;
    } else {
        return y;
    }
}

_pure bool pure_let(bool x) {
    bool y;
    y = x;
    return y;
}

_pure bool pure_id(bool x)
        _requires(x)
        _ensures(return == x)
{
    return x;
}

void test() {
    bool pure_let_result = pure_let(true);
    _assert(pure_let_result == true);
    _assert(pure_let_result == pure_let(true));
    _assert(pure_let(pure_let_result) == true);

    bool pure_not_result = pure_not(true);
    _assert(pure_not_result == false);
}

_pure int pure_ghost_stmt()
  _ensures(1 == 0)
{
  _ghost_stmt(assume False);
  return 1;
}
