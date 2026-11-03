#include "pal.h"
#include <stdint.h>

uint32_t possibly_unwritten(uint32_t n)
{
    uint32_t temporary;
    uint32_t i = 0;
    while (i < n)
        _invariant(i <= n)
        _invariant(_inline_pulse(
            Pulse.Lib.C.Palow.Scalar.uint32_t_pts_to_uninit $&(temporary)))
    {
        temporary = i;
        i = i + 1;
    }
    _ghost_stmt(let value = uint32_t_read $&(temporary));
    return 0;
}
