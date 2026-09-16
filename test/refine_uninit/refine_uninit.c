// Test: _refine_uninit — refinement that only applies to uninit predicates.
#include "pal.h"
#include <stdint.h>

_refine_uninit((bool) _inline_pulse(is_null $(this)))
typedef int *nullable_ptr;

void take_nullable(_out nullable_ptr p)
{
    /* The refinement says the pointer is NULL and the `_out` mode says it
       addresses storage; unwritten storage still occupies bytes at a real
       address, so the two cannot both hold and the body is vacuous. */
#ifdef PALOW
    _ghost_stmt(Pulse.Lib.C.Palow.CTypes.int32_t_pts_to_uninit_not_null $(p));
#else
    _ghost_stmt(Pulse.Lib.Reference.pts_to_uninit_not_null $(p));
#endif
    _ghost_stmt(unreachable());
}
