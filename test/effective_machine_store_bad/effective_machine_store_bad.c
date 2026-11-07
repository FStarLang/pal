#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* A store through a float lvalue does not reinterpret a declared integer. */
void store_float_into_declared_integer(void)
{
    uint32_t x = 0;
    *(float *)&x = 0.0f;
}
