#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

uint32_t store_allocated(void)
    _ensures(return == 0)
{
    uint32_t *p = malloc(sizeof *p);
    if (!p)
        return 0;
    *p = 0;
    uint32_t r = *p;
    free(p);
    return r;
}

/* calloc's zero bytes have no effective type: reads at different types are
   all defined, and none of them fixes a type. */
int32_t untyped_zero_reads(void)
    _ensures(return == 0)
{
    void *p = calloc(1, sizeof(uint32_t));
    if (!p)
        return 0;
    uint32_t a = *(uint32_t *)p;
    int32_t b = *(int32_t *)p;
    free(p);
    return b;
}

uint32_t copy_into_allocated(void)
    _ensures(return == 0 || return == 9)
{
    uint32_t s = 9;
    void *d = malloc(sizeof s);
    if (!d)
        return 0;
    memcpy(d, &s, sizeof s);
    uint32_t r = *(uint32_t *)d;
    free(d);
    return r;
}
