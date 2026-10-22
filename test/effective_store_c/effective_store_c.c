#include "pal.h"
#include <stdint.h>
#include <stdlib.h>

void store_float(void)
{
    void *p = malloc(16);
    if (!p)
        return;
    *(float *)p = 1.25f;
    free(p);
}

void store_pointer(void)
{
    void *p = malloc(16);
    if (!p)
        return;
    *(float **)p = NULL;
    free(p);
}
