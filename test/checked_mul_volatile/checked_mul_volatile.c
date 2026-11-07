#include "pal.h"
#include <stdint.h>

_Bool volatile_output(_out volatile uint32_t *result)
{
    return __builtin_mul_overflow(1u, 2u, result);
}
