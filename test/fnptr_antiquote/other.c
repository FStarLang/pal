#include "pal.h"

static int add1(int x) _requires(x < 50) _ensures(return == x + 1) {
    return x + 1;
}

typedef int (*unary)(int);

int call_other_add1(void) _ensures(return == 2) {
    unary f = add1;
    _assert(f == add1);
    return f(1);
}
