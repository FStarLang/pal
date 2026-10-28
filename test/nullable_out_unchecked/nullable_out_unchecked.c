#include "pal.h"
#include <stdint.h>

void write_optional_unchecked(_nullable _out int32_t *p)
{
    *p = 42;
}
