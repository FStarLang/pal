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

/* In Palow an allocation may fail, so a constructor's return type says so and
   what the `_ensures` promises holds only when there is an object. */
#ifdef PALOW
_allocated _nullable typedef R *R_optr;

R_optr whole_struct_assign(void)
    _ensures(return->x == 6 && return->y == 7)
{
    R *t = malloc(sizeof(*t));
    if (t == NULL) {
        return NULL;
    }
    *t = (R) { .x = 6, .y = 7 };
    return t;
}

R_optr field_by_field(void)
    _ensures(return->x == 6 && return->y == 7)
{
    R *t = malloc(sizeof(*t));
    if (t == NULL) {
        return NULL;
    }
    _ghost_stmt($unfold-uninit(R) $(t));
    t->x = 6;
    t->y = 7;
    return t;
}

R_optr field_by_field_cast(void)
    _ensures(return->x == 6 && return->y == 7)
{
    R *t = (R *) malloc(sizeof(*t));
    if (t == NULL) {
        return NULL;
    }
    _ghost_stmt($unfold-uninit(R) $(t));
    t->x = 6;
    t->y = 7;
    return t;
}
#else
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
#endif

void scalar_alloc(void) {
    int *p = malloc(sizeof(*p));
    if (p == NULL) {
        return;
    }
    *p = 42;
    free(p);
}

void array_alloc(void) {
    int *arr = malloc(sizeof(*arr) * 10);
    if (arr == NULL) {
        return;
    }
    _assert(arr._length == 10);
    free(arr);
}

void array_alloc_count_first(void) {
    int *arr = malloc(10 * sizeof(*arr));
    if (arr == NULL) {
        return;
    }
    _assert(arr._length == 10);
    free(arr);
}

void calloc_single(void) {
    R *t = calloc(1, sizeof(*t));
    if (t == NULL) {
        return;
    }
    _assert(t->x == 0);
    free(t);
}

void calloc_array(void) {
    int *arr = calloc(10, sizeof(*arr));
    if (arr == NULL) {
        return;
    }
    _assert(arr._length == 10);
    free(arr);
}
