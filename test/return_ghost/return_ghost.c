#include "pal.h"
#include <stdint.h>

// Custom postcondition predicate over the returned value, deliberately NOT
// auto-introducible, so establishing it requires an explicit ghost fold.
_include_pulse(Return_ghost_include1,
  let is_pos (x: Int32.t) : slprop = pure (Int32.v x > 0)

  ghost fn intro_is_pos (x: Int32.t)
    requires pure (Int32.v x > 0)
    ensures is_pos x
  {
    fold is_pos x
  }
)

// The body's final `return x` is followed only by a ghost statement that
// references `$(return)`. PAL emits this as
//   let return = x; intro_is_pos return; return return;
// so the ghost fold is live and can establish the `is_pos $(return)` ensures.
int pick_positive(int x)
  _requires(x > 0)
  _ensures(_inline_pulse(Return_ghost_include1.is_pos $(return)))
{
  return x;
  _ghost_stmt(Return_ghost_include1.intro_is_pos $(return));
}

// Multiple returns in one block: only the first (reachable) return is rewritten
// to bind `$(return)` for its trailing ghost; the second return is unreachable.
int pick_first(int a, int b)
  _requires(a > 0)
  _ensures(_inline_pulse(Return_ghost_include1.is_pos $(return)))
{
  return a;
  _ghost_stmt(Return_ghost_include1.intro_is_pos $(return));
  return b;
}

// The rewrite applies inside any block, not just at the end of the function:
// here the `return x` + ghost lives inside an `if` branch.
int pick_in_block(int x, int flag)
  _requires(x > 0)
  _ensures(_inline_pulse(Return_ghost_include1.is_pos $(return)))
{
  if (flag) {
    return x;
    _ghost_stmt(Return_ghost_include1.intro_is_pos $(return));
  }
  return x;
  _ghost_stmt(Return_ghost_include1.intro_is_pos $(return));
}
