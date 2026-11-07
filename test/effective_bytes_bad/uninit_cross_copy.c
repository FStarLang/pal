#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* Copying the bytes of an uninitialised uint32_t into a float leaves the
   float indeterminate, so the read is rejected. */
float copy_uninit_into_float(void)
{
    uint32_t s;
    float d = 1.0f;
    memcpy(&d, &s, sizeof d);
    return d;
}
