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

(* Implementation-defined pointer-to-long casts. Only the result type is
   specified: there are no numeric encoding or round-trip guarantees. *)
val core_to_int32 (r: core_ref) : FStar.Int32.t
val core_to_uint32 (r: core_ref) : FStar.UInt32.t
val core_to_int64 (r: core_ref) : FStar.Int64.t
val core_to_uint64 (r: core_ref) : FStar.UInt64.t

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

(* Conversion between a pointer and its numeric address, modeling the C casts
   `(uint64_t) p` and `(T * ) n`.

   Both are UNINTERPRETED, and that is the whole design. `core_ref_to_u64` says
   nothing about the integer it produces, so a program cannot learn anything
   about memory by looking at an address; `u64_to_core_ref` produces a pointer
   carrying NO ownership, so nothing can be read or written through it without
   a separately supplied `pts_to`. That keeps the integer-to-pointer direction
   sound rather than trusted: "address A holds an object of type T" is not a
   fact about the C program -- it comes from a linker script or a hardware
   manual -- so it has to be introduced deliberately, as an assumption, at the
   point where it is claimed.

   Deliberately absent:
     - any round-trip law. `u64_to_core_ref (core_ref_to_u64 p) == p` is NOT
       stated. C only guarantees a round trip via `uintptr_t` (C17 7.20.1.4p1),
       and a program relying on it relies on provenance rules PAL does not
       model.
     - `core_ref_to_u64 core_null == 0uL`. A null pointer's integer value is
       unspecified in C; only the integer *constant* 0 converts to a null
       pointer. It is 0 on every target PAL has been used on, but that is a
       platform fact, so a project needing it should assume it explicitly. *)
val core_ref_to_u64 (r: core_ref) : UInt64.t

val u64_to_core_ref (x: UInt64.t) : core_ref

instance has_zero_default_core_ref : has_zero_default core_ref = {
  zero_default = core_null
}

instance inhabited_core_ref : inhabited core_ref = {
  witness = core_null
}
