#include "pal.h"
#include <stdint.h>

/* An `_out` parameter whose `_ensures` is a predicate that owns it. The
   predicate's name starts with `pure`, but the clause is not a `pure` fact:
   the contract must not add the parameter's ownership a second time. If it
   did, the caller would hold two full permissions on `y` and could prove
   anything. */

_include_pulse(Purecell,
  let pure_cell (p: ptr) : slprop = exists* v. uint32_t_pts_to p 1.0R v
)

void ext(_out uint32_t *x)
  _ensures((_slprop)_inline_pulse(pure_cell $(x)));

void use(void)
  _ensures((_slprop)_inline_pulse(pure False))
{
  uint32_t y;
  ext(&y);
  _ghost_stmt(unfold Purecell.pure_cell $(&y); uint32_t_gather $(&y); uint32_t_reveal $(&y); mem_pts_to_perm_bound $(&y));
  _ghost_stmt(drop_ (exists* b. mem_pts_to $(&y) 2.0R b); rewrite emp as (uint32_t_pts_to $(&y) 1.0R 0ul));
}
