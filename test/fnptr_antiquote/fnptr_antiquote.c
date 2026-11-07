#include "pal.h"

/* An annotation names a function as C does: `$(add1)`, or a bare `add1` in a
   C annotation, is the function-pointer value, with its validity in scope.
   `add1` is TU-local, and other.c has a `static add1` of its own, so the name
   must also resolve to this file's function. */
static int add1(int x) _requires(x < 100) _ensures(return == x + 1) {
    return x + 1;
}

typedef int (*unary)(int);

int call_add1(void) _ensures(return == 8) {
    unary f = add1;
    _assert(f == add1);
    _ghost_stmt(Pulse.Lib.C.Palow.FnPtr.valid_cast $(add1) $(add1));
    return f(7);
}
