#include "pal.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* memset of part of a declared object is not a whole-object fill; it is
   refused rather than given a value. */
uint32_t zero_half(void)
{
    uint32_t x = 7;
    memset(&x, 0, 2);
    return x;
}
