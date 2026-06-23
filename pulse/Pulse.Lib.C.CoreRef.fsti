module Pulse.Lib.C.CoreRef
#lang-pulse
open Pulse
open Pulse.Lib.C.Inhabited
open Pulse.Lib.Reference

(* An axiomatized, non-parametric raw pointer, modeling a C raw pointer.

   Its purpose is to break the type- and predicate-level cycles that arise when
   translating (mutually) recursive C structs. A struct field annotated
   `_core_ref` is translated to `core_ref` instead of `ref T`, so:
     - the generated `noeq type` no longer mentions `T` — breaking the F*
       module/type dependency cycle (F* forbids cyclic module dependencies);
     - the field carries no automatically generated ownership predicate —
       breaking the otherwise non-terminating recursion of `..._pred`.

   The user recovers a typed reference from a `core_ref` with `core_to_ref` and
   reasons about ownership with the usual `pts_to`, writing the recursive
   ownership predicate by hand (e.g. via `_include_pulse`). *)

val core_ref : Type0

val core_null : core_ref

val core_is_null (r: core_ref) : (b: bool { b <==> r == core_null })

(* Reinterpret a typed reference as a raw pointer and back, modeling the C
   reinterpret casts between raw and typed pointers. *)
val ref_to_core (#a: Type u#a) (r: ref a) : core_ref

val core_to_ref (a: Type u#a) (r: core_ref) : ref a

(* Round-trip: casting a `ref a` to raw and back yields the original pointer. *)
val core_to_ref_to_core (#a: Type u#a) (r: ref a)
  : Lemma (core_to_ref a (ref_to_core r) == r)
          [SMTPat (ref_to_core r)]

(* Nullness is preserved by the cast. *)
val ref_to_core_is_null (#a: Type u#a) (r: ref a)
  : Lemma (core_is_null (ref_to_core r) == is_null r)
          [SMTPat (core_is_null (ref_to_core r))]

val ref_to_core_null (a: Type u#a)
  : Lemma (ref_to_core (null #a) == core_null)

(* Decidable pointer equality, with no preconditions. *)
val core_ref_eq (x y: core_ref) : (b: bool { b == true <==> x == y })

instance has_zero_default_core_ref : has_zero_default core_ref = {
  zero_default = core_null
}

instance inhabited_core_ref : inhabited core_ref = {
  witness = core_null
}
