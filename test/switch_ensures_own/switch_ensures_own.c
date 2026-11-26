#include "pal.h"
#include <stdint.h>

/*
 * A switch `_ensures` may state ownership that the generated frame does not
 * cover, here the cell a `_plain` parameter points to. Each clause has to
 * reach the match join on its own: folded into one conjunction with the
 * `_live` clause, the ownership clause would be read as a proposition.
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
        _ensures(_live(kind))
        _ensures(_inline_pulse(
            exists* value. Pulse.Lib.C.Palow.Scalar.uint32_t_pts_to $(_old(out)) 1.0R value))
        // clang-format on
    {
    case 1:
        *out = 10;
        break;
    case 2:
        *out = 20;
        break;
    default:
        break;
    }
}
