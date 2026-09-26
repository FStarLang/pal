#include "pal.h"
#include <stdlib.h>
#include <stdint.h>

void test_malloc_free(void) {
    int *p = (int *) malloc(sizeof(int));
    if (p == NULL) {
        return;
    }
    *p = 42;
    free(p);
}

typedef struct {
    int x;
    int y;
} point;

/* `_nullable` says the allocation may have failed, which is the honest
   contract for a constructor. Everything the `_ensures` promises about the
   object then holds only when there is one, and Palow states it that way: the
   clause goes inside the nullness guard, beside the ownership it speaks of.
   PAL's current emitter states the guard but leaves the clause outside it, so
   the promise is one the callee cannot keep, and the nullable spelling is
   Palow's alone. */
#ifdef PALOW
/* A separate name, because `point_ptr` is also what the functions that take an
   existing block are written against, and those are not nullable. */
_allocated _nullable typedef point *point_optr;
_allocated typedef point *point_ptr;

point_optr mk_point()
    _ensures((_specint) return->x + return->y == 13)
{
    point *p = malloc(sizeof(point));
    if (p == NULL) {
        return NULL;
    }
    *p = (point) { .x = 6, .y = 7 };
    return p;
}
#else
_allocated typedef point *point_ptr;

point_ptr mk_point()
    _ensures((_specint) return->x + return->y == 13)
{
    point *p = malloc(sizeof(point));
    *p = (point) { .x = 6, .y = 7 };
    return p;
}
#endif

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
    if (arr == NULL) {
        return;
    }
    _assert(arr._length == 10);
    free(arr);
}