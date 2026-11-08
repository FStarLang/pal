#include "pal.h"
#include <stdint.h>

_Bool wide_input(_out uint32_t *result)
{
    return __builtin_mul_overflow((unsigned __int128)1, 2u, result);
}
