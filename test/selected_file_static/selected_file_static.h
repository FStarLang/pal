#pragma once
#include "pal.h"
#include <stdint.h>

// A static body each translation unit has its own copy of. Its value comes
// from the including file.
static int32_t helper(void)
    _ensures(return == 3)
{
    return HELPER_VALUE;
}
