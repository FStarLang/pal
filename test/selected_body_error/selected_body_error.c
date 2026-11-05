#include "pal.h"
#include <stdint.h>

_Bool selected_error(_out uint32_t *result)
{
    return __builtin_mul_overflow(-1, 2u, result);
}

void other(void)
{
}
