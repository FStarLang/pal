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
    _ghost_stmt(
      unfold R.storage int32_t_ctype int32_t_alignof $(p) index_p;
      with actual. assert Pulse.Lib.C.Palow.Effective.Value.storage
        int32_t_ctype int32_t_alignof $(p) actual;
      Pulse.Lib.C.Palow.Effective.Value.reveal_storage
        int32_t_ctype int32_t_alignof $(p) #actual;
      with b. assert mem_pts_to_at $(p) 1.0R b actual;
      mem_pts_to_at_not_null $(p) #1.0R #b #actual;
      Pulse.Lib.C.Palow.Effective.Value.claim_storage
        int32_t_ctype int32_t_alignof $(p) #b #actual;
      fold R.storage int32_t_ctype int32_t_alignof $(p) index_p);
    _ghost_stmt(unreachable());
}
