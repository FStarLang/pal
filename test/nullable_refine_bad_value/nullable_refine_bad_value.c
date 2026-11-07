#include "pal.h"
#include <stddef.h>
#include <stdint.h>

void wrong_optional_value(_nullable _out _refine(*this == 42) int32_t *p)
{
    if (p != NULL) {
        *p = 17;
    }
}
