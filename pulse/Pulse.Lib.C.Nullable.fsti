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

(* [unless_null x p] holds [p] unless [x] is null, in which case it is [emp].

   The definition is deliberately hidden. It is a conditional on a runtime
   test, so wherever it is left to unfold the prover ends up staring at a
   `match` on the null test instead of at a slprop it can match structurally,
   and the [pulse_intro] rules below stop firing. That happens in exactly the
   place it hurts most: the join point of a null test that is not the last
   statement of its function, where the postcondition is inferred rather than
   written down. Keeping the abbreviation opaque outside this module means the
   only ways in and out are the introductions and eliminations here. *)
val unless_null (#t:Type0) {| has_is_null t |} (x:t) (p:slprop) : slprop

[@@pulse_intro]
ghost fn intro_unless_null_null (#t:Type0) {| has_is_null t |} (x:t) (p:slprop)
  requires pure (test_null x)
  ensures unless_null x p

[@@pulse_intro]
ghost fn intro_unless_null_nonnull (#t:Type0) {| has_is_null t |} (x:t) (p:slprop)
  requires p
  ensures unless_null x p

ghost fn elim_unless_null_null (#t:Type0) {| has_is_null t |} (x:t) (p:slprop)
  requires unless_null x p
  requires pure (test_null x)

ghost fn elim_unless_null_nonnull (#t:Type0) {| has_is_null t |} (x:t) (p:slprop)
  requires unless_null x p
  requires pure (not (test_null x))
  ensures p

(* The same, for the branch in which the pointer *is* null. There the resource
   is unavailable, so the only way to reach `unless_null` is from the nullness
   itself, which the branch hypothesis supplies. *)

[@@pulse_intro]
ghost fn intro_unless_null_null_ref (#a:Type0) (x:ref a) (p:slprop)
  requires pure (test_null #(ref a) x)
  ensures unless_null x p

[@@pulse_intro]
ghost fn intro_unless_null_null_array (#a:Type0) (x:array a) (p:slprop)
  requires pure (test_null #(array a) x)
  ensures unless_null x p

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

[@@pulse_intro]
ghost fn intro_unless_null_array (#a:Type0) (x:array a) (p:slprop)
  requires p
  ensures unless_null x p

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

ghost fn elim_null_ref (#a:Type0) (x:ref a) (#p:slprop)
  requires unless_null #(ref a) x p
  requires pure (test_null #(ref a) x)

ghost fn elim_unless_null_arr (#a:Type0) (x:array a) (#p:slprop)
  requires unless_null #(array a) x p
  requires pure (not (test_null #(array a) x))
  ensures p

ghost fn elim_null_arr (#a:Type0) (x:array a) (#p:slprop)
  requires unless_null #(array a) x p
  requires pure (test_null #(array a) x)

(* A null pointer, bound to a name.

   A call that declines several optional outputs at once passes the same
   `null` for each of them, and gets back one `unless_null null _` per
   declined output. Those guards are identical except for the resource they
   carry, and the resource is exactly what the elimination has to recover by
   matching. With more than one of them in scope the match is ambiguous, the
   prover falls back to the introduction rules, and the failure surfaces as an
   unresolved `has_is_null` on a type nobody wrote.

   Handing each declined output its own name splits the guards apart at the
   pointer instead of at the resource, which is a position the matcher can
   discriminate on. The value is still null and the post-condition says so, so
   nothing is hidden from the caller -- only from the term matcher, which is
   the point. *)
fn null_ref (a:Type0)
  requires emp
  returns r : ref a
  ensures pure (r == null #a)
