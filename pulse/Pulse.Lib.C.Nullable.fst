module Pulse.Lib.C.Nullable
#lang-pulse
open Pulse
open Pulse.Lib.C.Ref
open Pulse.Lib.C.Array

let unless_null (#t:Type0) {| has_is_null t |} (x:t) (p:slprop) : slprop =
  if test_null x then emp else p

[@@pulse_intro]
ghost fn intro_unless_null_null (#t:Type0) {| has_is_null t |} (x:t) (p:slprop)
  requires pure (test_null x)
  ensures unless_null x p
{
  rewrite emp as (unless_null x p);
}

[@@pulse_intro]
ghost fn intro_unless_null_nonnull (#t:Type0) {| has_is_null t |} (x:t) (p:slprop)
  requires p
  ensures unless_null x p
{
  if (test_null x) {
    drop_ p;
    rewrite emp as (unless_null x p);
  } else {
    rewrite p as (unless_null x p);
  }
}

ghost fn elim_unless_null_null (#t:Type0) {| has_is_null t |} (x:t) (p:slprop)
  requires unless_null x p
  requires pure (test_null x)
{
  rewrite (unless_null x p) as emp;
}

ghost fn elim_unless_null_nonnull (#t:Type0) {| has_is_null t |} (x:t) (p:slprop)
  requires unless_null x p
  requires pure (not (test_null x))
  ensures p
{
  rewrite (unless_null x p) as p;
}

(* The same, for the branch in which the pointer *is* null. There the resource
   is unavailable, so the only way to reach `unless_null` is from the nullness
   itself, which the branch hypothesis supplies. *)

[@@pulse_intro]
ghost fn intro_unless_null_null_ref (#a:Type0) (x:ref a) (p:slprop)
  requires pure (test_null #(ref a) x)
  ensures unless_null x p
{
  intro_unless_null_null #(ref a) x p;
}

[@@pulse_intro]
ghost fn intro_unless_null_null_array (#a:Type0) (x:array a) (p:slprop)
  requires pure (test_null #(array a) x)
  ensures unless_null x p
{
  intro_unless_null_null #(array a) x p;
}

(* The generic introduction above leaves `t` and its `has_is_null` instance to
   be recovered by unification. When the prover reaches for it while proving a
   postcondition, the goal it is matching against is often still partly a
   metavariable, and instance resolution then fails on `has_is_null ?t` rather
   than on anything the user wrote. These two restate the same rule at the two
   pointer-like types PAL actually produces, so the instance is fixed by the
   shape of the argument and never has to be guessed. *)

[@@pulse_intro]
ghost fn intro_unless_null_ref (#a:Type0) (x:ref a) (p:slprop)
  requires p
  ensures unless_null x p
{
  intro_unless_null_nonnull #(ref a) x p;
}

[@@pulse_intro]
ghost fn intro_unless_null_array (#a:Type0) (x:array a) (p:slprop)
  requires p
  ensures unless_null x p
{
  intro_unless_null_nonnull #(array a) x p;
}

(* Elimination with the guarded resource left implicit. PAL emits these on
   entry to a branch that has just tested a nullable pointer, where it knows
   which way the test went but not which resource the pointer is carrying at
   that point in the program -- an optional output starts uninitialized and
   becomes initialized part way through. Leaving `p` to be recovered by
   matching against whatever `unless_null` is in context removes the need to
   know. *)

ghost fn elim_unless_null_ref (#a:Type0) (x:ref a) (#p:slprop)
  requires unless_null #(ref a) x p
  requires pure (not (test_null #(ref a) x))
  ensures p
{
  elim_unless_null_nonnull #(ref a) x p;
}

ghost fn elim_null_ref (#a:Type0) (x:ref a) (#p:slprop)
  requires unless_null #(ref a) x p
  requires pure (test_null #(ref a) x)
{
  elim_unless_null_null #(ref a) x p;
}

ghost fn elim_unless_null_arr (#a:Type0) (x:array a) (#p:slprop)
  requires unless_null #(array a) x p
  requires pure (not (test_null #(array a) x))
  ensures p
{
  elim_unless_null_nonnull #(array a) x p;
}

ghost fn elim_null_arr (#a:Type0) (x:array a) (#p:slprop)
  requires unless_null #(array a) x p
  requires pure (test_null #(array a) x)
{
  elim_unless_null_null #(array a) x p;
}

fn null_ref (a:Type0)
  requires emp
  returns r : ref a
  ensures pure (r == null #a)
{
  null #a
}
