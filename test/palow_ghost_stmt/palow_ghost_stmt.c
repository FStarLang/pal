#include <assert.h>
#include "pal.h"
#include <stdint.h>

/* Ghost statements written against the Palow memory model.
 *
 * `_ghost_stmt` splices hand-written Pulse into the body, so the fragment
 * names whatever the surrounding model calls things. These fragments name
 * Palow's predicates, which the old translator has no definitions for, so this
 * test is `palow-only`. The C is still compiled, which is what keeps the
 * annotations honest as no-ops. */

/* A `ghost fn` is a statement, so `assume` here takes an slprop rather than a
 * prop. */
_pure int pure_ghost_stmt()
  _ensures(1 == 0)
{
  _ghost_stmt(assume (pure False));
  return 1;
}

/* Owning a pointee is already a proof that the pointer is not null, and in
 * Palow that lemma is named after the type stored, because the points-to
 * predicate is. */
void check_nonnull(const int *x) {
    _ghost_stmt(int32_t_pts_to_not_null $(x));
    assert(x);
}
