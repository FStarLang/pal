#include "pal.h"
#include <stdint.h>

_Bool narrow_output(_out uint16_t *result)
{
    return __builtin_mul_overflow(1u, 2u, result);
}
