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
    *(int *)p = 7;
    int result = *(int *)p;
    *(float *)p = 1.25f;
    float f = *(float *)p;
    *(double *)p = 2.5;
    double d = *(double *)p;
    *(struct point *)p = (struct point){ 11, 13 };
    free(p);
    return result;
}

void abandon_allocation(void)
{
    void *p = malloc(64);
    if (!p)
        return;
    free(p);
}

void join_stores(int flag)
{
    void *p = malloc(16);
    if (!p)
        return;
    if (flag)
        *(int *)p = 1;
    else
        *(int *)p = 2;
    *(int *)p = 3;
    free(p);
}

void allocation_across_loop(void)
{
    void *p = malloc(16);
    if (!p)
        return;
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

void store_after_abort(void)
{
    void *p = malloc(16);
    if (!p)
        abort();
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
