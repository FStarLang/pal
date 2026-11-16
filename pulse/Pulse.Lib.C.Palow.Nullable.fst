module Pulse.Lib.C.Palow.Nullable

(* ---------------------------------------------------------------------------
   Resources guarded by a nullness test.

   `unless_null a p` is `p` unless `a` is null, in which case it is `emp`. It is
   the shape of every allocation postcondition, since allocation may fail.

   This mirrors `Pulse.Lib.C.Nullable`, but is stated directly on Palow's `ptr`
   rather than through the `has_is_null` typeclass, so that the new memory model
   does not depend on the one it is meant to replace. The intro/elim pair is
   what clients need: a bare `rewrite` cannot see through the `if`, because the
   branch is only decided by a pure fact.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Ptr

let unless_null (a: ptr) (p: slprop) : slprop =
  if is_null a then emp else p

[@@pulse_intro]
ghost fn intro_unless_null_null (a: ptr) (p: slprop)
  requires pure (is_null a)
  ensures  unless_null a p
{
  rewrite emp as (unless_null a p);
}

[@@pulse_intro]
ghost fn intro_unless_null (a: ptr) (p: slprop)
  requires p
  ensures  unless_null a p
{
  if (is_null a) {
    drop_ p;
    rewrite emp as (unless_null a p);
  } else {
    rewrite p as (unless_null a p);
  }
}

(* Ambiguity is harmless here: every guard on a null pointer is `emp`, so a
   call that declines several optional outputs can discard them in any order. *)
[@@allow_ambiguous]
ghost fn elim_unless_null_null (a: ptr) (p: slprop)
  requires unless_null a p
  requires pure (is_null a)
{
  rewrite (unless_null a p) as emp;
}

ghost fn elim_unless_null (a: ptr) (p: slprop)
  requires unless_null a p
  requires pure (not (is_null a))
  ensures  p
{
  rewrite (unless_null a p) as p;
}

(* `null_or a p q` is `p` if `a` is null and `q` otherwise. A `_cursor_from(s)`
   parameter's slot is one: when the seed `s` is null the slot holds the
   cursor, and when it is not, the slot is only storage. *)
let null_or (a: ptr) (p q: slprop) : slprop =
  if is_null a then p else q

ghost fn elim_null_or_null (a: ptr) (p q: slprop)
  requires null_or a p q
  requires pure (is_null a)
  ensures  p
{
  rewrite (null_or a p q) as p;
}

ghost fn elim_null_or (a: ptr) (p q: slprop)
  requires null_or a p q
  requires pure (not (is_null a))
  ensures  q
{
  rewrite (null_or a p q) as q;
}
