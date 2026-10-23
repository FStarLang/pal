#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* A declared object cannot be retyped by a callee either. */
void store_float(float *p)
{
    *p = 1.0f;
}

void retype_declared(void)
{
    uint32_t x = 0;
    store_float((float *)&x);
}
