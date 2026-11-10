#include "pal.h"

/* In a single-file build, an annotation names a function as C does: `$(add1)`,
   or a bare `add1` in a C annotation, is the function-pointer value. */
int add1(int x) _requires(x < 100) _ensures(return == x + 1) {
    return x + 1;
}

typedef int (*unary)(int);

int call_add1(void) _ensures(return == 8) {
    unary f = add1;
    _assert(f == add1);
    _ghost_stmt(Pulse.Lib.C.Palow.FnPtr.valid_cast $(add1) $(add1));
    return f(7);
}

/* A parameter or local named like a function shadows it, in annotations as in
   C: `add1` and `$(add1)` below are the variable, not the function. */
int param_shadows(int add1) _requires(add1 < 10) _ensures(return == add1 + 1) {
    _assert(add1 < 10);
    _ghost_stmt(assert pure (Int32.v $(add1) < 10));
    return add1 + 1;
}

int local_shadows(void) _ensures(return == 4) {
    int add1 = 3;
    _assert(add1 == 3);
    _ghost_stmt(assert pure (Int32.v $(add1) == 3));
    return add1 + 1;
}
