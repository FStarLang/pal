// Allocation sizes spelled with an *expression* operand of `sizeof`, i.e. the
// common C idiom `p = malloc(sizeof(*p))`, are recognized just like the
// type-operand spelling `malloc(sizeof(T))`.
#include "pal.h"
#include <stdlib.h>
#include <stdint.h>

typedef struct R {
    int x;
    int y;
} R;

_allocated typedef R *R_ptr;

R_ptr whole_struct_assign(void)
    _ensures(return->x == 6 && return->y == 7)
{
    R *t = malloc(sizeof(*t));
    *t = (R) { .x = 6, .y = 7 };
    return t;
}

R_ptr field_by_field(void)
    _ensures(return->x == 6 && return->y == 7)
{
    R *t = malloc(sizeof(*t));
    _ghost_stmt($unfold-uninit(R) $(t));
    t->x = 6;
    t->y = 7;
    return t;
}

R_ptr field_by_field_cast(void)
    _ensures(return->x == 6 && return->y == 7)
{
    R *t = (R *) malloc(sizeof(*t));
    _ghost_stmt($unfold-uninit(R) $(t));
    t->x = 6;
    t->y = 7;
    return t;
}

void scalar_alloc(void) {
    int *p = malloc(sizeof(*p));
    *p = 42;
    free(p);
}

void array_alloc(void) {
    int *arr = malloc(sizeof(*arr) * 10);
    _assert(arr._length == 10);
    free(arr);
}

void array_alloc_count_first(void) {
    int *arr = malloc(10 * sizeof(*arr));
    _assert(arr._length == 10);
    free(arr);
}

void calloc_single(void) {
    R *t = calloc(1, sizeof(*t));
    _assert(t->x == 0);
    free(t);
}

void calloc_array(void) {
    int *arr = calloc(10, sizeof(*arr));
    _assert(arr._length == 10);
    free(arr);
}
