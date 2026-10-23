#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* A character store into fresh storage defines one byte; a uint32_t read
   needs all four. */
uint32_t read_partially_written(void)
{
    void *p = malloc(4);
    if (!p)
        return 0;
    *(unsigned char *)p = 1;
    uint32_t r = *(uint32_t *)p;
    free(p);
    return r;
}
