#include "pal.h"
#include <stdint.h>

/*
 * As `switch_block_case`, but one block case gives the cell away to a
 * function that keeps it, so the switch's ownership `_ensures` does not hold
 * at the join.
 */
void keep(_plain uint32_t *p)
    _requires(_inline_pulse(
        exists* value. Pulse.Lib.C.Palow.Scalar.uint32_t_pts_to $(p) 1.0R value));

// clang-format off
void set_by_kind(_plain uint32_t *out, uint32_t kind)
    _requires(_inline_pulse(
        exists* value. Pulse.Lib.C.Palow.Scalar.uint32_t_pts_to $(out) 1.0R value))
    _ensures(_inline_pulse(
        exists* value. Pulse.Lib.C.Palow.Scalar.uint32_t_pts_to $(out) 1.0R value))
// clang-format on
{
    switch (kind)
        // clang-format off
        _ensures(_inline_pulse(
            exists* value. Pulse.Lib.C.Palow.Scalar.uint32_t_pts_to $(_old(out)) 1.0R value))
        // clang-format on
    {
    case 1:
        {
            uint32_t v = 10;
            *out = v;
            break;
        }
    case 2:
        {
            keep(out);
            break;
        }
    default:
        break;
    }
}
