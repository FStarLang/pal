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

/* memset writes bytes, not a type: a declared object keeps its declared type
   and holds whatever value those bytes spell. */
uint32_t zero_preserves_type(void)
    _ensures(return == 0)
{
    uint32_t x = 7;
    memset(&x, 0, 4);
    return x;
}

uint32_t fill_preserves_type(void)
    _ensures(return == 0x01010101)
{
    uint32_t x = 7;
    memset(&x, 1, sizeof x);
    return x;
}

/* All-zero bytes are +0.0 on an Annex F target. */
float zero_declared_float(void)
{
    float x = 1.0f;
    memset(&x, 0, sizeof x);
    return x;
}

/* A copy into a declared object keeps the destination's declared type: the
   bytes of a uint32_t are read back as a float, and as a uint32_t again. */
uint32_t declared_cross_type_copy(uint32_t s)
    _ensures(return == s)
{
    float d = 1.0f;
    memcpy(&d, &s, sizeof d);
    uint32_t r = 0;
    memcpy(&r, &d, sizeof r);
    return r;
}
