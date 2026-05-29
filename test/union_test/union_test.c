#include "pal.h"

union foo {
    int x;
    _Bool y;
};

void set_x(union foo *f) {
    f->x = 42;
    _assert(f->x == 42);
}

void set_y(union foo *f) {
    f->x = 67;
    f->y = 1;
    _assert(f->y);
}

void compound_literal(union foo *f) {
    *f = (union foo) { .x = 67 };
    _assert(f->x == 67);
}

void initializer() {
    union foo f = { .x = 67 };
    _assert(f.x == 67);
}

void check_active(union foo *f) {
    f->x = 42;
    _assert(f->x._active);
}