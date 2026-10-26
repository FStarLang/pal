#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* A copy gives allocated storage the source's effective type, so an earlier
   float store does not survive copying an integer over it. */
float read_float_after_integer_copy(void)
{
    float *p = malloc(sizeof *p);
    if (!p)
        return 0.0f;
    *p = 1.0f;
    uint32_t s = 1;
    memcpy(p, &s, sizeof s);
    float r = *p;
    free(p);
    return r;
}
