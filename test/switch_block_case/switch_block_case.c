#include "pal.h"
#include <stdint.h>

/*
 * Cases written as blocks, `case v: { ...; break; }`, end in a `break` too:
 * the switch is one `match`, so its ownership `_ensures` is the join. Each
 * block declares a local of its own.
 */
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
            {
                uint32_t w = 20;
                *out = w;
            }
            break;
        }
    default:
        {
            break;
        }
    }
}
