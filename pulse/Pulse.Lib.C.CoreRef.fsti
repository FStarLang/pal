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

(* And the other way round: an address viewed at a type and erased again is the
   address it started as. The two lemmas together say that the two views name
   the same machine word, which is exactly what the C cast means -- and the
   second direction is what a caller needs after it has recovered a typed
   pointer from a slot and has to name the raw address again to talk about the
   loan the callee gave it. *)
val ref_to_core_to_ref (a: Type u#a) (r: core_ref)
  : Lemma (ref_to_core (core_to_ref a r) == r)
          [SMTPat (core_to_ref a r)]

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

(* ---------------------------------------------------------------------- *)
(* Raw pointer cells.                                                      *)
(*                                                                         *)
(* The C idiom `f((void const ** )&typedLocal)` hands a callee the caller's *)
(* own pointer slot at an erased type, so that the callee can write a       *)
(* pointer into it without knowing what it points at. It is how every       *)
(* "acquire a buffer" interface is spelled.                                 *)
(*                                                                         *)
(* This is not the `ref_to_core` coercion. That one erases the type of a    *)
(* pointer value; this one changes the type at which a cell holding a       *)
(* pointer is viewed. A cell holds one machine word either way, so the two  *)
(* views denote the same location -- but they are different F* types, so    *)
(* the ownership has to be moved between them explicitly, and the value in  *)
(* the cell re-read through `ref_to_core`/`core_to_ref` at the same time.   *)
(* Hence a view shift rather than a coercion.                               *)

val core_cell (#a: Type u#a) (r: ref (ref a)) : ref core_ref

(* The view shift is a bijection on locations, so distinct typed cells stay
   distinct when viewed raw. Without this, two acquires into two different
   locals would be indistinguishable to the prover. *)
val core_cell_injective (#a: Type u#a) (r1 r2: ref (ref a))
  : Lemma (requires core_cell r1 == core_cell r2)
          (ensures r1 == r2)

ghost fn to_core_cell (#a: Type0) (r: ref (ref a)) (#p: perm) (#v: ref a)
  requires pts_to r #p v
  ensures pts_to (core_cell r) #p (ref_to_core v)

ghost fn of_core_cell (#a: Type0) (r: ref (ref a)) (#p: perm) (#w: core_ref)
  requires pts_to (core_cell r) #p w
  ensures pts_to r #p (core_to_ref a w)

(* An out-parameter is handed uninitialized storage, which has no value to
   re-read; the shift is then just a retyping of the slot. *)
ghost fn to_core_cell_uninit (#a: Type0) (r: ref (ref a))
  requires pts_to_uninit r
  ensures pts_to_uninit (core_cell r)

(* The same shift for the way C actually reaches an empty slot. A local passed
   to an out-parameter is nearly always initialized to NULL first, so what the
   caller holds is a value it is about to lose rather than nothing at all.
   Taking `pts_to_uninit` here would force every such call site to forget the
   value by hand, and taking `pts_to` would exclude the genuinely uninitialized
   local, so this takes `initialized_or_not` and covers both. *)
val initialized_or_not (#a: Type0) (r: ref a) : slprop

[@@pulse_intro]
ghost fn intro_initialized_or_not (#a: Type0) (r: ref a) (#v: a)
  requires pts_to r v
  ensures initialized_or_not r

[@@pulse_intro]
ghost fn intro_initialized_or_not_uninit (#a: Type0) (r: ref a)
  requires pts_to_uninit r
  ensures initialized_or_not r

ghost fn to_core_cell_out (#a: Type0) (r: ref (ref a))
  requires initialized_or_not r
  ensures pts_to_uninit (core_cell r)

ghost fn of_core_cell_uninit (#a: Type0) (r: ref (ref a))
  requires pts_to_uninit (core_cell r)
  ensures pts_to_uninit r
