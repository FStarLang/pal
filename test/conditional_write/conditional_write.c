#include "pal.h"
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

_include_pulse(Conditional_write_include,
  module R = Pulse.Lib.Reference

  // Ownership of `p` after `maybe_write`: if `b` we wrote a value (initialized),
  // otherwise the cell is still uninitialized.
  let maybe_pts_to (b: bool) (p: ref Int32.t) : slprop =
    if b then (exists* (v: Int32.t). R.pts_to p v) else R.pts_to_uninit p

  // --- intro lemmas: package the branch resource into `maybe_pts_to` ---
  [@@pulse_intro]
  ghost fn intro_maybe_pts_to_init (b: bool) (p: ref Int32.t) (#v: Int32.t)
    requires R.pts_to p v ** pure b
    ensures maybe_pts_to b p
  {
    if b {
      introduce exists* (w: Int32.t). R.pts_to p w with v;
      rewrite (exists* (w: Int32.t). R.pts_to p w) as (maybe_pts_to b p);
    } else {
      unreachable ();
    }
  }

  [@@pulse_intro]
  ghost fn intro_maybe_pts_to_uninit (b: bool) (p: ref Int32.t)
    requires R.pts_to_uninit p ** pure (not b)
    ensures maybe_pts_to b p
  {
    if b {
      unreachable ();
    } else {
      rewrite (R.pts_to_uninit p) as (maybe_pts_to b p);
    }
  }

  // --- elim lemmas: recover the concrete resource from `maybe_pts_to` ---
  ghost fn elim_maybe_pts_to_init (#p: ref Int32.t) (b: bool)
    requires maybe_pts_to b p ** pure b
    ensures exists* (v: Int32.t). R.pts_to p v
  {
    if b {
      rewrite (maybe_pts_to b p) as (exists* (w: Int32.t). R.pts_to p w);
    } else {
      unreachable ();
    }
  }

  ghost fn elim_maybe_pts_to_uninit (#p: ref Int32.t) (b: bool)
    requires maybe_pts_to b p ** pure (not b)
    ensures R.pts_to_uninit p
  {
    if b {
      unreachable ();
    } else {
      rewrite (maybe_pts_to b p) as (R.pts_to_uninit p);
    }
  }
)

// Takes an uninitialized `int *` and a bool, and only writes through the
// pointer when the bool is true. Its postcondition is therefore conditional:
// initialized when `b`, still uninitialized when `!b`. `_out _plain` opts out
// of the automatic ownership spec so we can state the conditional one by hand,
// while `_out` still makes the caller borrow the cell as uninitialized.
void maybe_write(_out _plain int *p, bool b)
  _requires(_inline_pulse(Pulse.Lib.Reference.pts_to_uninit $(p)))
  _ensures(_inline_pulse(Conditional_write_include.maybe_pts_to $(b) $(p)))
{
    if (b) {
        *p = 42;
        _ghost_stmt(Conditional_write_include.intro_maybe_pts_to_init $(b) $(p));
    } else {
        _ghost_stmt(Conditional_write_include.intro_maybe_pts_to_uninit $(b) $(p));
    }
}

// Borrow cell 0 of an uninitialized array, hand it to `maybe_write`, then give
// the cell back. Because `maybe_write`'s output is conditional, the caller must
// pick the return lemma based on `b`: when the cell was written we return it
// with `array_return_cell` (initialized); when it was left untouched we return
// it with `array_return_cell_uninit`.
void caller(_plain _array int *a, bool b)
  _requires(_inline_pulse(exists* (y: array_spec Int32.t). array_pts_to_uninit $(a) y))
  _requires(a._length >= 1)
  _ensures(_inline_pulse(exists* (s: array_spec Int32.t). array_pts_to $(a) 1.0R s))
{
    maybe_write(&a[0], b);
    if (b) {
        _ghost_stmt(Conditional_write_include.elim_maybe_pts_to_init $(b));
        _ghost_stmt(array_return_cell $(a) 0sz);
    } else {
        _ghost_stmt(Conditional_write_include.elim_maybe_pts_to_uninit $(b));
        _ghost_stmt(array_return_cell_uninit $(a) 0sz);
    }
}
