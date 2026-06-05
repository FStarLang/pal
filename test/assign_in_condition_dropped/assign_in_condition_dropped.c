#include "pal.h"
#include <stdint.h>

int32_t if_assign_pure_inlined(int32_t n)
{
    int32_t half;
    if ((half = n / 2) != 0) {
        return half;
    }
    return -1;
}