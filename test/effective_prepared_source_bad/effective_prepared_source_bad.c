#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* Fresh allocated storage has no value, so it is no copy source. */
float copy_from_fresh(void)
{
    void *p = malloc(sizeof(float));
    if (!p)
        return 0.0f;
    float d = 0.0f;
    memcpy(&d, p, sizeof d);
    free(p);
    return d;
}
