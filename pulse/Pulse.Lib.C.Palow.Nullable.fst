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
