/* Test: mutable globals in the contract of a function this file only declares.
 *
 * The functions below are defined in another translation unit, so their
 * prototypes are all a caller here has to go on. `_live(g)` on a prototype has
 * to give the declaration the same ownership it gives a definition: dropped,
 * the declaration would publish a signature that leaves `g` alone, and every
 * caller would be checked against that.
 */

#include "pal.h"
#include <stdint.h>

uint32_t counter;
extern uint32_t shared;

void reset(void) _requires(_live(counter)) _ensures(_live(counter))
    _ensures(counter == 0);
void touch_shared(void) _preserves(_live(shared));

/* 1. What the callee promises about the global reaches the caller. */
uint32_t reset_then_read(void) _preserves(_live(counter)) _ensures(return == 0) {
  reset();
  return counter;
}

/* 2. An `extern` global, handed to the callee and back. */
void pass_shared(void) _preserves(_live(shared)) { touch_shared(); }

/* 3. And the callee does take it: what the caller knew of the value does not
 *    survive the call. When a declaration's `_live` was dropped, this
 *    verified, because the frame kept `shared` across a call that may write
 *    it. The same claim without the call verifies, so the failure is the
 *    call's and not a name that does not resolve. */
#ifdef PALOW
_include_pulse(Global_prototype_check,
  fn keeps_shared_alone (v: erased UInt32.t)
    requires uint32_t_pts_to Global_shared.addr_var_shared 1.0R v
    ensures  uint32_t_pts_to Global_shared.addr_var_shared 1.0R v
  {
    ()
  }

  [@@expect_failure]
  fn keeps_shared (v: erased UInt32.t)
    requires uint32_t_pts_to Global_shared.addr_var_shared 1.0R v
    ensures  uint32_t_pts_to Global_shared.addr_var_shared 1.0R v
  {
    Func_touch_shared.func_touch_shared ();
  }
)
#else
_include_pulse(Global_prototype_check,
  fn keeps_shared_alone (v: erased Typedef_uint32_t.ty_uint32_t)
    requires Global_shared.addr_var_shared |-> v
    ensures  Global_shared.addr_var_shared |-> v
  {
    ()
  }

  [@@expect_failure]
  fn keeps_shared (v: erased Typedef_uint32_t.ty_uint32_t)
    requires Global_shared.addr_var_shared |-> v
    ensures  Global_shared.addr_var_shared |-> v
  {
    Func_touch_shared.func_touch_shared ();
  }
)
#endif
