#include "pal.h"
#include <stddef.h>
#include <stdint.h>

void leave_optional_unwritten(_nullable _out int32_t *p)
{
    if (p != NULL) {
    }
}
