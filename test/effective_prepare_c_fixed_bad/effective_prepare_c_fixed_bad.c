#include "pal.h"
#include <stdint.h>

/* A declared object keeps its declared type: an incompatible store through
   a cast cannot retype it (C11 6.5p6-7). */
void store_declared(void)
{
    int declared = 7;
    *(float *)&declared = 1.25f;
}
