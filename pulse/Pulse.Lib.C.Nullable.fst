module Pulse.Lib.C.Nullable
#lang-pulse
open Pulse
open Pulse.Lib.C.Ref
open Pulse.Lib.C.Array

(* A typeclass for pointer-like types that have a notion of being null. *)
class has_is_null (t:Type0) = {
  test_null : t -> bool;
}

instance has_is_null_ref (a:Type0) : has_is_null (ref a) = {
  test_null = (fun r -> is_null r);
}

instance has_is_null_array (a:Type0) : has_is_null (array a) = {
  test_null = (fun r -> array_is_null r);
}

(* [unless_null x p] holds [p] unless [x] is null, in which case it is [emp]. *)
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
