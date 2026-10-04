#include "pal.h"
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

/*
 * An unsigned 32-bit literal compared with or converted to size_t must be
 * zero-extended. PAL used to print the literal's stored value, which for
 * 4294967295U is -1, giving `-1sz` -- rejected by F*, and the wrong number.
 */

bool above_u32_max(size_t x)
    _ensures(return == (x > 4294967295))
{
    return x > UINT32_MAX;
}

bool above_u32_lit(size_t x)
    _ensures(return == (x > 4294967295))
{
    return x > 4294967295U;
}

size_t u32_max_as_size(void)
    _ensures(return == 4294967295)
{
    return (size_t)UINT32_MAX;
}
