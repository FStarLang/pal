#include "pal.h"
#include <stdint.h>
#include <stdbool.h>

void missing_storage(_plain uint32_t *result)
    _requires(_inline_pulse(emp))
{
    bool overflow = __builtin_mul_overflow(6u, 7u, result);
}
