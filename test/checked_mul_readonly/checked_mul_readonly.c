#include "pal.h"
#include <stdint.h>
#include <stdbool.h>

// clang-format off
void cannot_write_readonly(_plain const uint32_t *result)
    _requires(_inline_pulse(
        exists* value. Pulse.Lib.C.Palow.Scalar.uint32_t_pts_to $(result) 0.5R value))
    _ensures(_inline_pulse(
        exists* value. Pulse.Lib.C.Palow.Scalar.uint32_t_pts_to $(result) 0.5R value))
// clang-format on
{
    bool overflow = __builtin_mul_overflow(6u, 7u, (uint32_t *)result);
}
