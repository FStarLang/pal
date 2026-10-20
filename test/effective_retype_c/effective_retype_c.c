#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

void abort(void) _ensures(false);

struct point { int x; int y; };

int retype_allocated(void)
    _ensures(return == 0 || return == 7)
{
    void *p = malloc(64);
    if (!p)
        return 0;
    _ghost_stmt($prepare(int) $(p));
    *(int *)p = 7;
    int result = *(int *)p;
    _ghost_stmt($prepare(float) $(p));
    *(float *)p = 1.25f;
    float f = *(float *)p;
    _ghost_stmt($prepare(double) $(p));
    *(double *)p = 2.5;
    double d = *(double *)p;
    _ghost_stmt($prepare(struct point) $(p));
    *(struct point *)p = (struct point){ 11, 13 };
    free(p);
    return result;
}

void abandon_prepared(void)
{
    void *p = malloc(64);
    if (!p)
        return;
    _ghost_stmt($prepare(double) $(p));
    free(p);
}

void join_prepared(int flag)
{
    void *p = malloc(16);
    if (!p)
        return;
    if (flag)
        _ghost_stmt($prepare(int) $(p));
    else
        _ghost_stmt($prepare(int) $(p));
    *(int *)p = 3;
    free(p);
}

void prepared_across_loop(void)
{
    void *p = malloc(16);
    if (!p)
        return;
    _ghost_stmt($prepare(double) $(p));
    int i = 0;
    while (i < 2)
        _invariant(0 <= i && i <= 2)
    {
        ++i;
    }
    free(p);
}

void initialized_prefix_loop(void)
{
    void *p = malloc(16);
    if (!p)
        return;
    _ghost_stmt($prepare(int) $(p));
    *(int *)p = 1;
    int i = 0;
    while (i < 2)
        _invariant(0 <= i && i <= 2)
    {
        *(int *)p = i;
        ++i;
    }
    free(p);
}

void prepare_after_abort(void)
{
    void *p = malloc(16);
    if (!p)
        abort();
    _ghost_stmt($prepare(int) $(p));
    *(int *)p = 9;
    free(p);
}

int calloc_nonsticky(void)
    _ensures(return == 0)
{
    void *p = calloc(1, 16);
    if (!p)
        return 0;
    int a = *(int *)p;
    int64_t b = *(int64_t *)p;
    int c = *(int *)p;
    free(p);
    return a + c;
}

int memset_nonsticky(void)
    _ensures(return == 0)
{
    void *p = malloc(16);
    if (!p)
        return 0;
    memset(p, 0, 16);
    int a = *(int *)p;
    int64_t b = *(int64_t *)p;
    int c = *(int *)p;
    free(p);
    return a + c;
}

unsigned long long rank_value_only(unsigned long long value)
    _ensures(return == value)
{
    return value;
}
