#include "pal.h"
#include <stdint.h>

_Bool wide_output(_out uint64_t *result)
{
    return __builtin_mul_overflow(1u, 2u, result);
}
