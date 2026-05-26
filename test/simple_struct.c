#include "pal.h"

struct simple {
    int x, *y, **z;
};

void foo(struct simple *s) {
    **s->z = 42;
}