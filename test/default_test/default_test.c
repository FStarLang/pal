#include "pal.h"
#include <stdlib.h>

typedef struct {
    int x;
    int y;
} point;

_pure int zero;

_pure point zero_point;

void test_globals() {
    _assert(zero == 0);
    _assert(zero_point.x == 0);
}

void test_calloc_ref(void) {
    int *p = (int *) calloc(1, sizeof(int));
    _assert(*p == 0);
    free(p);
}

void test_calloc_array() {
    point *array = (point *) calloc(1 + 0, sizeof(point));
    _assert(array._length == 1);
    _assert(array[0].x == 0);
    array[0] = (point) {.x=67, .y=42};
    free(array);
}
