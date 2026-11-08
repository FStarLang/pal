#include "pal.h"
#include <stdint.h>

_Bool signed_input(_out uint32_t *result)
{
    return __builtin_mul_overflow(-1, 2u, result);
}
