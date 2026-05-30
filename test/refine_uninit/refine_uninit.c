// Test: _refine_uninit — refinement that only applies to uninit predicates.
#include "pal.h"
#include <stdint.h>

_refine_uninit((bool) _inline_pulse(is_null $(this)))
typedef int *nullable_ptr;

void take_nullable(_out nullable_ptr p)
{
    _ghost_stmt(Pulse.Lib.Reference.pts_to_uninit_not_null $(p));
    _ghost_stmt(unreachable());
}
