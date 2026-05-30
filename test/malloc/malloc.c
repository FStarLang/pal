#include "pal.h"
#include <stdlib.h>
#include <stdint.h>

void test_malloc_free(void) {
    int *p = (int *) malloc(sizeof(int));
    *p = 42;
    free(p);
}

typedef struct {
    int x;
    int y;
} point;

_allocated typedef point *point_ptr;

point_ptr mk_point()
    _ensures((_specint) return->x + return->y == 13)
{
    point *p = malloc(sizeof(point));
    *p = (point) { .x = 6, .y = 7 };
    return p;
}

_let(bool int32_fits(_specint x), INT32_MIN <= x && x <= INT32_MAX)

int sum_point(const point_ptr p)
    _requires(int32_fits((_specint) p->x + p->y))
    _ensures(return == _old(p->x + p->y))
{
    return p->x + p->y;
}

int sum_and_free_point(_consumes point_ptr p)
    _requires(int32_fits((_specint) p->x + p->y))
    _ensures(return == _old(p->x + p->y))
{
    int sum = sum_point(p);
    free(p);
    return sum;
}

void test_array_malloc_free(void) {
    int *arr = (int *) malloc(sizeof(int) * 10);
    _assert(arr._length == 10);
    free(arr);
}