module Pulse.Lib.C.RefRo
open Pulse
module R = Pulse.Lib.Reference
#lang-pulse

/// Read-only ownership of a reference's storage.
///
/// The motivating client is PAL's address-of-global support. PAL reads a
/// `_pure` global with *no* ownership at all: a read of `g` emits
/// the pure spec value `var_g` directly, with nothing in the `requires`. That
/// is only sound because the storage backing `g` is assumed to hold `var_g`
/// forever. So any pointer PAL hands out to a global must be read-only
/// *forever* -- a writable alias would let a callee store some other value
/// while PAL-emitted reads still evaluate to `var_g`, which is a contradiction.
///
/// `pts_to_ro` enforces that by hiding the permission under an existential.
/// `R.read` needs only `r |-> Frac p v` for some `p`, so reads still work,
/// but `R.write` / `( := )` require *full* ownership, which can never be
/// derived from an existentially quantified `p`.
///
/// The permission must stay existential rather than being fixed to some small
/// concrete fraction: a fixed fraction `k` could be acquired `n` times and
/// gathered to `n * k`, and `R.pts_to_perm_bound` (which ensures `p <=. 1.0R`)
/// would then prove `False` for `n > 1/k`. With an existential, `n` acquires
/// only constrain `p_1 + ... + p_n <= 1.0R`, which is satisfiable for every `n`.
/// That is what makes `&g` usable any number of times, independently, by any
/// number of callers.
///
/// This must stay `unfold`. As an opaque `let`, the struct-global case breaks:
/// Pulse's `[@@pulse_intro] __aux_raw_unfold` only fires on a literal `pts_to`.
/// Unfolded, a read is just `R.op_Bang r`, which needs no wrapper of its own.
unfold
let pts_to_ro (#[@@@mkey] a:Type u#a) ([@@@mkey] r: R.ref a) (v: a) : slprop =
  exists* p. R.pts_to r #p v

/// Release read-only ownership.
///
/// `&g` conjures `pts_to_ro` out of `emp`, so a function that takes the address
/// of a global must give the ownership back before returning (in PAL, via
/// `_ghost_stmt(drop_ro ...)` after the `return`). Dropping is
/// always sound here: the permission is a fraction of the one reserved for the
/// global at program start, and nothing was ever written through it.
ghost
fn drop_ro u#a (#a:Type u#a) (r: R.ref a) (#v: a)
  requires pts_to_ro r v
  ensures emp
{
  with p. assert (R.pts_to r #p v);
  drop_ (R.pts_to r #p v)
}
