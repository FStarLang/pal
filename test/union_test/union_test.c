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

union foo copy_x(const union foo *f)
    _requires(f->x._active)
    _ensures(return.x._active)
    _ensures(return.x == f->x)
{
    return *f;
}

union foo copy_y(const union foo *f)
    _requires(f->y._active)
    _ensures(return.y._active)
    _ensures(return.y == f->y)
{
    return *f;
}

union foo local_y(void)
    _ensures(return.y._active)
    _ensures(return.y)
{
    union foo f;
    f.y = 1;
    return f;
}

union foo copied_local(int x)
    _ensures(return.x._active)
    _ensures(return.x == x)
{
    union foo f = { .x = x };
    union foo g = f;
    return g;
}