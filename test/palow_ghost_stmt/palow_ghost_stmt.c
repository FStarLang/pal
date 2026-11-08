#include <assert.h>
#include "pal.h"
#include <stdint.h>

/* Ghost statements written against the Palow memory model.
 *
 * `_ghost_stmt` splices hand-written Pulse into the body, so the fragments
 * name Palow's predicates directly. */

/* A `ghost fn` is a statement, so `assume` here takes an slprop rather than a
 * prop. */
_pure int pure_ghost_stmt()
  _ensures(1 == 0)
{
  _ghost_stmt(assume (pure False));
  return 1;
}

/* Reveal the actual indexed bytes to prove nonnull, then restore the same
 * retained owner without discarding its effective-type information. */
void check_nonnull(const int *x) {
    _ghost_stmt(
      unfold R.value int32_t_ctype int32_t_repr int32_t_alignof
        $(x) perm_x val_x index_x;
      with actual. assert Pulse.Lib.C.Palow.Effective.Value.value
        int32_t_ctype int32_t_repr int32_t_alignof $(x) perm_x val_x actual;
      Pulse.Lib.C.Palow.Effective.Value.reveal_value
        int32_t_ctype int32_t_repr int32_t_alignof $(x) #perm_x #val_x #actual;
      with b. assert mem_pts_to_at $(x) perm_x b actual;
      mem_pts_to_at_not_null $(x) #perm_x #b #actual;
      Pulse.Lib.C.Palow.Effective.Value.claim
        int32_t_ctype int32_t_repr int32_t_alignof $(x) #perm_x #val_x #b #actual;
      R.conceal int32_t_ctype int32_t_repr int32_t_alignof
        $(x) #perm_x #val_x #actual #index_x);
    assert(x);
}
