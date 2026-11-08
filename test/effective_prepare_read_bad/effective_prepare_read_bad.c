#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* Fresh allocated storage holds no value to read. */
uint32_t read_fresh(void)
{
    uint32_t *p = malloc(sizeof *p);
    if (!p)
        return 0;
    uint32_t r = *p;
    free(p);
    return r;
}
