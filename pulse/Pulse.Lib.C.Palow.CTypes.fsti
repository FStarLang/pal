module Pulse.Lib.C.Palow.CTypes

(* ---------------------------------------------------------------------------
   The remaining C scalar types.

   `Pulse.Lib.C.Palow.Scalar` derives `uint8_t`, `uint32_t` and stored pointers
   by hand, as the exemplar. This module is the rest of the set, written in
   exactly the shape PAL will emit: for each C scalar type, a size, a
   representation relation, a points-to predicate, a write-only view, and the
   seven resource lemmas that PAL's proof automation consumes. Nothing here is
   an axiom -- every one of these is a consequence of the layer-0 interface,
   which is the property that has to hold for the per-type emission strategy to
   be viable at all.

   The uniformity is the point. These blocks were mechanically generated from a
   table of (name, F* type, size, signedness), which is precisely the
   information the translator has. Signed types differ from unsigned ones only
   in composing `Encoding.to_bits` with the value, and `_Bool` only in mapping
   `true`/`false` to 1/0; the rest is identical, and the derived lemmas are
   textually the same for every type.

   Sizes are the LP64 values, matching the rest of Palow and what clang reports
   for the targets PAL supports.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow.Encoding
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Array
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.Float

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64

(* ------------------------------- bool_t ------------------------------- *)

let bool_t_sizeof : SZ.t = 1sz
let bool_t_alignof : SZ.t = 1sz

let bool_t_repr (x: bool) (b: bytes) : prop =
  b == encode (SZ.v bool_t_sizeof) None (if x then 1 else 0)

val bool_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: bool) : slprop


val bool_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop


val bool_t_repr_no_prov (x: bool) (b: bytes)
  : Lemma (requires bool_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v bool_t_sizeof)


val bool_t_repr_injective (x y: bool) (b: bytes)
  : Lemma (requires bool_t_repr x b /\ bool_t_repr y b)
          (ensures  x == y)


ghost fn bool_t_pts_to_not_null (a: ptr) (#p: perm) (#x: bool)
  preserves bool_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


(* Unwritten storage is still storage: it occupies bool_t_sizeof bytes at a real
   address, so the pointer to it cannot be NULL. This is what makes an `_out`
   parameter refined to be NULL vacuous rather than merely unprovable. *)
ghost fn bool_t_pts_to_uninit_not_null (a: ptr)
  preserves bool_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


[@@allow_ambiguous]
ghost fn bool_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: bool)
  preserves bool_t_pts_to a p1 x
  preserves bool_t_pts_to a p2 y
  ensures   pure (x == y)


ghost fn bool_t_share (a: ptr) (#p: perm) (#x: bool)
  requires bool_t_pts_to a p x
  ensures  bool_t_pts_to a (p /. 2.0R) x ** bool_t_pts_to a (p /. 2.0R) x


[@@allow_ambiguous]
ghost fn bool_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: bool)
  requires bool_t_pts_to a p1 x ** bool_t_pts_to a p2 y
  ensures  bool_t_pts_to a (p1 +. p2) x ** pure (x == y)


ghost fn bool_t_reveal (a: ptr) (#p: perm) (#x: bool)
  requires bool_t_pts_to a p x
  ensures  exists* b. mem_pts_to a p b ** pure (bool_t_repr x b)


ghost fn bool_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: bool)
  requires mem_pts_to a p b
  requires pure (bool_t_repr x b)
  ensures  bool_t_pts_to a p x


ghost fn bool_t_forget (a: ptr) (#x: bool)
  requires bool_t_pts_to a 1.0R x
  ensures  bool_t_pts_to_uninit a


ghost fn bool_t_claim (a: ptr) (#b: bytes) (x: bool)
  requires mem_pts_to a 1.0R b
  requires pure (bool_t_repr x b)
  ensures  bool_t_pts_to a 1.0R x

(* Raw storage of the right size is write-only ownership at this type, and back
   again: the two directions an allocation and a deallocation take. *)
ghost fn bool_t_claim_uninit (a: ptr) (#b: bytes)
  requires mem_pts_to a 1.0R b
  requires pure (len b == SZ.v bool_t_sizeof)
  ensures  bool_t_pts_to_uninit a


ghost fn bool_t_reveal_uninit (a: ptr)
  requires bool_t_pts_to_uninit a
  ensures  exists* b. mem_pts_to a 1.0R b ** pure (len b == SZ.v bool_t_sizeof)



(* ------------------------------- int8_t ------------------------------- *)

let int8_t_sizeof : SZ.t = 1sz
let int8_t_alignof : SZ.t = 1sz

let int8_t_repr (x: I8.t) (b: bytes) : prop =
  b == encode (SZ.v int8_t_sizeof) None (to_bits 8 (I8.v x))

val int8_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: I8.t) : slprop


val int8_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop


val int8_t_repr_no_prov (x: I8.t) (b: bytes)
  : Lemma (requires int8_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v int8_t_sizeof)


val int8_t_repr_injective (x y: I8.t) (b: bytes)
  : Lemma (requires int8_t_repr x b /\ int8_t_repr y b)
          (ensures  x == y)


ghost fn int8_t_pts_to_not_null (a: ptr) (#p: perm) (#x: I8.t)
  preserves int8_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


(* Unwritten storage is still storage: it occupies int8_t_sizeof bytes at a real
   address, so the pointer to it cannot be NULL. This is what makes an `_out`
   parameter refined to be NULL vacuous rather than merely unprovable. *)
ghost fn int8_t_pts_to_uninit_not_null (a: ptr)
  preserves int8_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


[@@allow_ambiguous]
ghost fn int8_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: I8.t)
  preserves int8_t_pts_to a p1 x
  preserves int8_t_pts_to a p2 y
  ensures   pure (x == y)


ghost fn int8_t_share (a: ptr) (#p: perm) (#x: I8.t)
  requires int8_t_pts_to a p x
  ensures  int8_t_pts_to a (p /. 2.0R) x ** int8_t_pts_to a (p /. 2.0R) x


[@@allow_ambiguous]
ghost fn int8_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: I8.t)
  requires int8_t_pts_to a p1 x ** int8_t_pts_to a p2 y
  ensures  int8_t_pts_to a (p1 +. p2) x ** pure (x == y)


ghost fn int8_t_reveal (a: ptr) (#p: perm) (#x: I8.t)
  requires int8_t_pts_to a p x
  ensures  exists* b. mem_pts_to a p b ** pure (int8_t_repr x b)


ghost fn int8_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: I8.t)
  requires mem_pts_to a p b
  requires pure (int8_t_repr x b)
  ensures  int8_t_pts_to a p x


ghost fn int8_t_forget (a: ptr) (#x: I8.t)
  requires int8_t_pts_to a 1.0R x
  ensures  int8_t_pts_to_uninit a


ghost fn int8_t_claim (a: ptr) (#b: bytes) (x: I8.t)
  requires mem_pts_to a 1.0R b
  requires pure (int8_t_repr x b)
  ensures  int8_t_pts_to a 1.0R x

(* Raw storage of the right size is write-only ownership at this type, and back
   again: the two directions an allocation and a deallocation take. *)
ghost fn int8_t_claim_uninit (a: ptr) (#b: bytes)
  requires mem_pts_to a 1.0R b
  requires pure (len b == SZ.v int8_t_sizeof)
  ensures  int8_t_pts_to_uninit a


ghost fn int8_t_reveal_uninit (a: ptr)
  requires int8_t_pts_to_uninit a
  ensures  exists* b. mem_pts_to a 1.0R b ** pure (len b == SZ.v int8_t_sizeof)



(* ------------------------------- int16_t ------------------------------- *)

let int16_t_sizeof : SZ.t = 2sz
let int16_t_alignof : SZ.t = 2sz

let int16_t_repr (x: I16.t) (b: bytes) : prop =
  b == encode (SZ.v int16_t_sizeof) None (to_bits 16 (I16.v x))

val int16_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: I16.t) : slprop


val int16_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop


val int16_t_repr_no_prov (x: I16.t) (b: bytes)
  : Lemma (requires int16_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v int16_t_sizeof)


val int16_t_repr_injective (x y: I16.t) (b: bytes)
  : Lemma (requires int16_t_repr x b /\ int16_t_repr y b)
          (ensures  x == y)


ghost fn int16_t_pts_to_not_null (a: ptr) (#p: perm) (#x: I16.t)
  preserves int16_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


(* Unwritten storage is still storage: it occupies int16_t_sizeof bytes at a real
   address, so the pointer to it cannot be NULL. This is what makes an `_out`
   parameter refined to be NULL vacuous rather than merely unprovable. *)
ghost fn int16_t_pts_to_uninit_not_null (a: ptr)
  preserves int16_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


[@@allow_ambiguous]
ghost fn int16_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: I16.t)
  preserves int16_t_pts_to a p1 x
  preserves int16_t_pts_to a p2 y
  ensures   pure (x == y)


ghost fn int16_t_share (a: ptr) (#p: perm) (#x: I16.t)
  requires int16_t_pts_to a p x
  ensures  int16_t_pts_to a (p /. 2.0R) x ** int16_t_pts_to a (p /. 2.0R) x


[@@allow_ambiguous]
ghost fn int16_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: I16.t)
  requires int16_t_pts_to a p1 x ** int16_t_pts_to a p2 y
  ensures  int16_t_pts_to a (p1 +. p2) x ** pure (x == y)


ghost fn int16_t_reveal (a: ptr) (#p: perm) (#x: I16.t)
  requires int16_t_pts_to a p x
  ensures  exists* b. mem_pts_to a p b ** pure (int16_t_repr x b)


ghost fn int16_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: I16.t)
  requires mem_pts_to a p b
  requires pure (int16_t_repr x b)
  ensures  int16_t_pts_to a p x


ghost fn int16_t_forget (a: ptr) (#x: I16.t)
  requires int16_t_pts_to a 1.0R x
  ensures  int16_t_pts_to_uninit a


ghost fn int16_t_claim (a: ptr) (#b: bytes) (x: I16.t)
  requires mem_pts_to a 1.0R b
  requires pure (int16_t_repr x b)
  ensures  int16_t_pts_to a 1.0R x

(* Raw storage of the right size is write-only ownership at this type, and back
   again: the two directions an allocation and a deallocation take. *)
ghost fn int16_t_claim_uninit (a: ptr) (#b: bytes)
  requires mem_pts_to a 1.0R b
  requires pure (len b == SZ.v int16_t_sizeof)
  ensures  int16_t_pts_to_uninit a


ghost fn int16_t_reveal_uninit (a: ptr)
  requires int16_t_pts_to_uninit a
  ensures  exists* b. mem_pts_to a 1.0R b ** pure (len b == SZ.v int16_t_sizeof)



(* ------------------------------- int32_t ------------------------------- *)

let int32_t_sizeof : SZ.t = 4sz
let int32_t_alignof : SZ.t = 4sz

let int32_t_repr (x: I32.t) (b: bytes) : prop =
  b == encode (SZ.v int32_t_sizeof) None (to_bits 32 (I32.v x))

val int32_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: I32.t) : slprop


val int32_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop


val int32_t_repr_no_prov (x: I32.t) (b: bytes)
  : Lemma (requires int32_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v int32_t_sizeof)


val int32_t_repr_injective (x y: I32.t) (b: bytes)
  : Lemma (requires int32_t_repr x b /\ int32_t_repr y b)
          (ensures  x == y)


ghost fn int32_t_pts_to_not_null (a: ptr) (#p: perm) (#x: I32.t)
  preserves int32_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


(* Unwritten storage is still storage: it occupies int32_t_sizeof bytes at a real
   address, so the pointer to it cannot be NULL. This is what makes an `_out`
   parameter refined to be NULL vacuous rather than merely unprovable. *)
ghost fn int32_t_pts_to_uninit_not_null (a: ptr)
  preserves int32_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


[@@allow_ambiguous]
ghost fn int32_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: I32.t)
  preserves int32_t_pts_to a p1 x
  preserves int32_t_pts_to a p2 y
  ensures   pure (x == y)


ghost fn int32_t_share (a: ptr) (#p: perm) (#x: I32.t)
  requires int32_t_pts_to a p x
  ensures  int32_t_pts_to a (p /. 2.0R) x ** int32_t_pts_to a (p /. 2.0R) x


[@@allow_ambiguous]
ghost fn int32_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: I32.t)
  requires int32_t_pts_to a p1 x ** int32_t_pts_to a p2 y
  ensures  int32_t_pts_to a (p1 +. p2) x ** pure (x == y)


ghost fn int32_t_reveal (a: ptr) (#p: perm) (#x: I32.t)
  requires int32_t_pts_to a p x
  ensures  exists* b. mem_pts_to a p b ** pure (int32_t_repr x b)


ghost fn int32_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: I32.t)
  requires mem_pts_to a p b
  requires pure (int32_t_repr x b)
  ensures  int32_t_pts_to a p x


ghost fn int32_t_forget (a: ptr) (#x: I32.t)
  requires int32_t_pts_to a 1.0R x
  ensures  int32_t_pts_to_uninit a


ghost fn int32_t_claim (a: ptr) (#b: bytes) (x: I32.t)
  requires mem_pts_to a 1.0R b
  requires pure (int32_t_repr x b)
  ensures  int32_t_pts_to a 1.0R x

(* Raw storage of the right size is write-only ownership at this type, and back
   again: the two directions an allocation and a deallocation take. *)
ghost fn int32_t_claim_uninit (a: ptr) (#b: bytes)
  requires mem_pts_to a 1.0R b
  requires pure (len b == SZ.v int32_t_sizeof)
  ensures  int32_t_pts_to_uninit a


ghost fn int32_t_reveal_uninit (a: ptr)
  requires int32_t_pts_to_uninit a
  ensures  exists* b. mem_pts_to a 1.0R b ** pure (len b == SZ.v int32_t_sizeof)



(* ------------------------------- int64_t ------------------------------- *)

let int64_t_sizeof : SZ.t = 8sz
let int64_t_alignof : SZ.t = 8sz

let int64_t_repr (x: I64.t) (b: bytes) : prop =
  b == encode (SZ.v int64_t_sizeof) None (to_bits 64 (I64.v x))

val int64_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: I64.t) : slprop


val int64_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop


val int64_t_repr_no_prov (x: I64.t) (b: bytes)
  : Lemma (requires int64_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v int64_t_sizeof)


val int64_t_repr_injective (x y: I64.t) (b: bytes)
  : Lemma (requires int64_t_repr x b /\ int64_t_repr y b)
          (ensures  x == y)


ghost fn int64_t_pts_to_not_null (a: ptr) (#p: perm) (#x: I64.t)
  preserves int64_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


(* Unwritten storage is still storage: it occupies int64_t_sizeof bytes at a real
   address, so the pointer to it cannot be NULL. This is what makes an `_out`
   parameter refined to be NULL vacuous rather than merely unprovable. *)
ghost fn int64_t_pts_to_uninit_not_null (a: ptr)
  preserves int64_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


[@@allow_ambiguous]
ghost fn int64_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: I64.t)
  preserves int64_t_pts_to a p1 x
  preserves int64_t_pts_to a p2 y
  ensures   pure (x == y)


ghost fn int64_t_share (a: ptr) (#p: perm) (#x: I64.t)
  requires int64_t_pts_to a p x
  ensures  int64_t_pts_to a (p /. 2.0R) x ** int64_t_pts_to a (p /. 2.0R) x


[@@allow_ambiguous]
ghost fn int64_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: I64.t)
  requires int64_t_pts_to a p1 x ** int64_t_pts_to a p2 y
  ensures  int64_t_pts_to a (p1 +. p2) x ** pure (x == y)


ghost fn int64_t_reveal (a: ptr) (#p: perm) (#x: I64.t)
  requires int64_t_pts_to a p x
  ensures  exists* b. mem_pts_to a p b ** pure (int64_t_repr x b)


ghost fn int64_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: I64.t)
  requires mem_pts_to a p b
  requires pure (int64_t_repr x b)
  ensures  int64_t_pts_to a p x


ghost fn int64_t_forget (a: ptr) (#x: I64.t)
  requires int64_t_pts_to a 1.0R x
  ensures  int64_t_pts_to_uninit a


ghost fn int64_t_claim (a: ptr) (#b: bytes) (x: I64.t)
  requires mem_pts_to a 1.0R b
  requires pure (int64_t_repr x b)
  ensures  int64_t_pts_to a 1.0R x

(* Raw storage of the right size is write-only ownership at this type, and back
   again: the two directions an allocation and a deallocation take. *)
ghost fn int64_t_claim_uninit (a: ptr) (#b: bytes)
  requires mem_pts_to a 1.0R b
  requires pure (len b == SZ.v int64_t_sizeof)
  ensures  int64_t_pts_to_uninit a


ghost fn int64_t_reveal_uninit (a: ptr)
  requires int64_t_pts_to_uninit a
  ensures  exists* b. mem_pts_to a 1.0R b ** pure (len b == SZ.v int64_t_sizeof)



(* ------------------------------- uint16_t ------------------------------- *)

let uint16_t_sizeof : SZ.t = 2sz
let uint16_t_alignof : SZ.t = 2sz

let uint16_t_repr (x: U16.t) (b: bytes) : prop =
  b == encode (SZ.v uint16_t_sizeof) None (U16.v x)

val uint16_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: U16.t) : slprop


val uint16_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop


val uint16_t_repr_no_prov (x: U16.t) (b: bytes)
  : Lemma (requires uint16_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v uint16_t_sizeof)


val uint16_t_repr_injective (x y: U16.t) (b: bytes)
  : Lemma (requires uint16_t_repr x b /\ uint16_t_repr y b)
          (ensures  x == y)


ghost fn uint16_t_pts_to_not_null (a: ptr) (#p: perm) (#x: U16.t)
  preserves uint16_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


(* Unwritten storage is still storage: it occupies uint16_t_sizeof bytes at a real
   address, so the pointer to it cannot be NULL. This is what makes an `_out`
   parameter refined to be NULL vacuous rather than merely unprovable. *)
ghost fn uint16_t_pts_to_uninit_not_null (a: ptr)
  preserves uint16_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


[@@allow_ambiguous]
ghost fn uint16_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: U16.t)
  preserves uint16_t_pts_to a p1 x
  preserves uint16_t_pts_to a p2 y
  ensures   pure (x == y)


ghost fn uint16_t_share (a: ptr) (#p: perm) (#x: U16.t)
  requires uint16_t_pts_to a p x
  ensures  uint16_t_pts_to a (p /. 2.0R) x ** uint16_t_pts_to a (p /. 2.0R) x


[@@allow_ambiguous]
ghost fn uint16_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: U16.t)
  requires uint16_t_pts_to a p1 x ** uint16_t_pts_to a p2 y
  ensures  uint16_t_pts_to a (p1 +. p2) x ** pure (x == y)


ghost fn uint16_t_reveal (a: ptr) (#p: perm) (#x: U16.t)
  requires uint16_t_pts_to a p x
  ensures  exists* b. mem_pts_to a p b ** pure (uint16_t_repr x b)


ghost fn uint16_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: U16.t)
  requires mem_pts_to a p b
  requires pure (uint16_t_repr x b)
  ensures  uint16_t_pts_to a p x


ghost fn uint16_t_forget (a: ptr) (#x: U16.t)
  requires uint16_t_pts_to a 1.0R x
  ensures  uint16_t_pts_to_uninit a


ghost fn uint16_t_claim (a: ptr) (#b: bytes) (x: U16.t)
  requires mem_pts_to a 1.0R b
  requires pure (uint16_t_repr x b)
  ensures  uint16_t_pts_to a 1.0R x

(* Raw storage of the right size is write-only ownership at this type, and back
   again: the two directions an allocation and a deallocation take. *)
ghost fn uint16_t_claim_uninit (a: ptr) (#b: bytes)
  requires mem_pts_to a 1.0R b
  requires pure (len b == SZ.v uint16_t_sizeof)
  ensures  uint16_t_pts_to_uninit a


ghost fn uint16_t_reveal_uninit (a: ptr)
  requires uint16_t_pts_to_uninit a
  ensures  exists* b. mem_pts_to a 1.0R b ** pure (len b == SZ.v uint16_t_sizeof)



(* ------------------------------- uint64_t ------------------------------- *)

let uint64_t_sizeof : SZ.t = 8sz
let uint64_t_alignof : SZ.t = 8sz

let uint64_t_repr (x: U64.t) (b: bytes) : prop =
  b == encode (SZ.v uint64_t_sizeof) None (U64.v x)

val uint64_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: U64.t) : slprop


val uint64_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop


val uint64_t_repr_no_prov (x: U64.t) (b: bytes)
  : Lemma (requires uint64_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v uint64_t_sizeof)


val uint64_t_repr_injective (x y: U64.t) (b: bytes)
  : Lemma (requires uint64_t_repr x b /\ uint64_t_repr y b)
          (ensures  x == y)


ghost fn uint64_t_pts_to_not_null (a: ptr) (#p: perm) (#x: U64.t)
  preserves uint64_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


(* Unwritten storage is still storage: it occupies uint64_t_sizeof bytes at a real
   address, so the pointer to it cannot be NULL. This is what makes an `_out`
   parameter refined to be NULL vacuous rather than merely unprovable. *)
ghost fn uint64_t_pts_to_uninit_not_null (a: ptr)
  preserves uint64_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


[@@allow_ambiguous]
ghost fn uint64_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: U64.t)
  preserves uint64_t_pts_to a p1 x
  preserves uint64_t_pts_to a p2 y
  ensures   pure (x == y)


ghost fn uint64_t_share (a: ptr) (#p: perm) (#x: U64.t)
  requires uint64_t_pts_to a p x
  ensures  uint64_t_pts_to a (p /. 2.0R) x ** uint64_t_pts_to a (p /. 2.0R) x


[@@allow_ambiguous]
ghost fn uint64_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: U64.t)
  requires uint64_t_pts_to a p1 x ** uint64_t_pts_to a p2 y
  ensures  uint64_t_pts_to a (p1 +. p2) x ** pure (x == y)


ghost fn uint64_t_reveal (a: ptr) (#p: perm) (#x: U64.t)
  requires uint64_t_pts_to a p x
  ensures  exists* b. mem_pts_to a p b ** pure (uint64_t_repr x b)


ghost fn uint64_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: U64.t)
  requires mem_pts_to a p b
  requires pure (uint64_t_repr x b)
  ensures  uint64_t_pts_to a p x


ghost fn uint64_t_forget (a: ptr) (#x: U64.t)
  requires uint64_t_pts_to a 1.0R x
  ensures  uint64_t_pts_to_uninit a


ghost fn uint64_t_claim (a: ptr) (#b: bytes) (x: U64.t)
  requires mem_pts_to a 1.0R b
  requires pure (uint64_t_repr x b)
  ensures  uint64_t_pts_to a 1.0R x

(* Raw storage of the right size is write-only ownership at this type, and back
   again: the two directions an allocation and a deallocation take. *)
ghost fn uint64_t_claim_uninit (a: ptr) (#b: bytes)
  requires mem_pts_to a 1.0R b
  requires pure (len b == SZ.v uint64_t_sizeof)
  ensures  uint64_t_pts_to_uninit a


ghost fn uint64_t_reveal_uninit (a: ptr)
  requires uint64_t_pts_to_uninit a
  ensures  exists* b. mem_pts_to a 1.0R b ** pure (len b == SZ.v uint64_t_sizeof)



(* -------------------------------- size_t --------------------------------

   `size_t` is not a fixed-width type in C, but PAL already commits to a
   concrete target (LP64) everywhere else, so it is eight bytes here. F*'s
   `FStar.SizeT.fits` is abstract, so the bound that `encode` needs is not
   derivable and has to be assumed -- exactly as for `Ptr.addr_bound`, and
   recorded alongside it under "Known deviations". *)

val size_t_bound (x: SZ.t) : Lemma (SZ.v x < pow2 64) [SMTPat (SZ.v x)]

(* LP64 again: `size_t` is sixty-four bits wide, so `FStar.SizeT.fits_u64`
   holds. F* keeps it abstract, so the conversions out of the fixed-width
   unsigned types are unavailable without assuming it -- the same assumption as
   `size_t_bound`, stated where the casts need it. *)

val sizet_of_uint16 (x: U16.t) : Pure SZ.t (requires True) (ensures fun y -> SZ.v y == U16.v x)

val sizet_of_uint32 (x: U32.t) : Pure SZ.t (requires True) (ensures fun y -> SZ.v y == U32.v x)

val sizet_of_uint64 (x: U64.t) : Pure SZ.t (requires True) (ensures fun y -> SZ.v y == U64.v x)

(* The same assumption once more, in the form arithmetic needs it.  `SZ.add`
   and friends carry a `fits` precondition, and on an LP64 target every value
   that fits in sixty-four bits satisfies it.  Stated with an `SMTPat` so a
   `size_t` addition whose bound the source has already established does not
   need a hint at every use. *)

val size_t_fits (x: int) : Lemma (requires 0 <= x /\ x < pow2 64) (ensures SZ.fits x)
  [SMTPat (SZ.fits x)]


let size_t_sizeof : SZ.t = 8sz
let size_t_alignof : SZ.t = 8sz

let size_t_repr (x: SZ.t) (b: bytes) : prop =
  b == encode (SZ.v size_t_sizeof) None (SZ.v x)

val size_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: SZ.t) : slprop


val size_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop


val size_t_repr_no_prov (x: SZ.t) (b: bytes)
  : Lemma (requires size_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v size_t_sizeof)


val size_t_repr_injective (x y: SZ.t) (b: bytes)
  : Lemma (requires size_t_repr x b /\ size_t_repr y b)
          (ensures  x == y)


ghost fn size_t_pts_to_not_null (a: ptr) (#p: perm) (#x: SZ.t)
  preserves size_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


(* Unwritten storage is still storage: it occupies size_t_sizeof bytes at a real
   address, so the pointer to it cannot be NULL. This is what makes an `_out`
   parameter refined to be NULL vacuous rather than merely unprovable. *)
ghost fn size_t_pts_to_uninit_not_null (a: ptr)
  preserves size_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


[@@allow_ambiguous]
ghost fn size_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: SZ.t)
  preserves size_t_pts_to a p1 x
  preserves size_t_pts_to a p2 y
  ensures   pure (x == y)


ghost fn size_t_share (a: ptr) (#p: perm) (#x: SZ.t)
  requires size_t_pts_to a p x
  ensures  size_t_pts_to a (p /. 2.0R) x ** size_t_pts_to a (p /. 2.0R) x


[@@allow_ambiguous]
ghost fn size_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: SZ.t)
  requires size_t_pts_to a p1 x ** size_t_pts_to a p2 y
  ensures  size_t_pts_to a (p1 +. p2) x ** pure (x == y)


ghost fn size_t_reveal (a: ptr) (#p: perm) (#x: SZ.t)
  requires size_t_pts_to a p x
  ensures  exists* b. mem_pts_to a p b ** pure (size_t_repr x b)


ghost fn size_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: SZ.t)
  requires mem_pts_to a p b
  requires pure (size_t_repr x b)
  ensures  size_t_pts_to a p x


ghost fn size_t_forget (a: ptr) (#x: SZ.t)
  requires size_t_pts_to a 1.0R x
  ensures  size_t_pts_to_uninit a


ghost fn size_t_claim (a: ptr) (#b: bytes) (x: SZ.t)
  requires mem_pts_to a 1.0R b
  requires pure (size_t_repr x b)
  ensures  size_t_pts_to a 1.0R x

(* Raw storage of the right size is write-only ownership at this type, and back
   again: the two directions an allocation and a deallocation take. *)
ghost fn size_t_claim_uninit (a: ptr) (#b: bytes)
  requires mem_pts_to a 1.0R b
  requires pure (len b == SZ.v size_t_sizeof)
  ensures  size_t_pts_to_uninit a


ghost fn size_t_reveal_uninit (a: ptr)
  requires size_t_pts_to_uninit a
  ensures  exists* b. mem_pts_to a 1.0R b ** pure (len b == SZ.v size_t_sizeof)




(* ------------------------------- uint8_t -------------------------------

   `uint8_t`'s size, representation and points-to are in
   `Pulse.Lib.C.Palow.Scalar`, where the aggregate proofs need them; only the
   derived set is missing, and it is the same set as every other type's. *)

val uint8_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop


val uint8_t_repr_no_prov (x: U8.t) (b: bytes)
  : Lemma (requires uint8_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v uint8_t_sizeof)


val uint8_t_repr_injective (x y: U8.t) (b: bytes)
  : Lemma (requires uint8_t_repr x b /\ uint8_t_repr y b)
          (ensures  x == y)


ghost fn uint8_t_pts_to_not_null (a: ptr) (#p: perm) (#x: U8.t)
  preserves uint8_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


(* Unwritten storage is still storage: it occupies uint8_t_sizeof bytes at a real
   address, so the pointer to it cannot be NULL. This is what makes an `_out`
   parameter refined to be NULL vacuous rather than merely unprovable. *)
ghost fn uint8_t_pts_to_uninit_not_null (a: ptr)
  preserves uint8_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


[@@allow_ambiguous]
ghost fn uint8_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: U8.t)
  preserves uint8_t_pts_to a p1 x
  preserves uint8_t_pts_to a p2 y
  ensures   pure (x == y)


ghost fn uint8_t_share (a: ptr) (#p: perm) (#x: U8.t)
  requires uint8_t_pts_to a p x
  ensures  uint8_t_pts_to a (p /. 2.0R) x ** uint8_t_pts_to a (p /. 2.0R) x


[@@allow_ambiguous]
ghost fn uint8_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: U8.t)
  requires uint8_t_pts_to a p1 x ** uint8_t_pts_to a p2 y
  ensures  uint8_t_pts_to a (p1 +. p2) x ** pure (x == y)


ghost fn uint8_t_forget (a: ptr) (#x: U8.t)
  requires uint8_t_pts_to a 1.0R x
  ensures  uint8_t_pts_to_uninit a


ghost fn uint8_t_claim (a: ptr) (#b: bytes) (x: U8.t)
  requires mem_pts_to a 1.0R b
  requires pure (uint8_t_repr x b)
  ensures  uint8_t_pts_to a 1.0R x

(* Raw storage of the right size is write-only ownership at this type, and back
   again: the two directions an allocation and a deallocation take. *)
ghost fn uint8_t_claim_uninit (a: ptr) (#b: bytes)
  requires mem_pts_to a 1.0R b
  requires pure (len b == SZ.v uint8_t_sizeof)
  ensures  uint8_t_pts_to_uninit a


ghost fn uint8_t_reveal_uninit (a: ptr)
  requires uint8_t_pts_to_uninit a
  ensures  exists* b. mem_pts_to a 1.0R b ** pure (len b == SZ.v uint8_t_sizeof)


(* ---------------------------------------------------------------------------
   Elements of an array

   `array_focus` hands back an `elem_pts_to t_repr`, which is the generic
   "there exist bytes representing this value" form. Every scalar type has its
   own points-to predicate instead, so each one gets a pair of ghost functions
   trading between the two. They are what makes an emitted subscript short: the
   value stays implicit throughout, so PAL never has to name `Seq.index xs i`.
   --------------------------------------------------------------------------- *)

ghost fn bool_t_of_elem (a: ptr) (#p: perm) (#x: bool)
  requires elem_pts_to bool_t_repr a p x
  ensures  bool_t_pts_to a p x


ghost fn bool_t_to_elem (a: ptr) (#p: perm) (#x: bool)
  requires bool_t_pts_to a p x
  ensures  elem_pts_to bool_t_repr a p x


ghost fn int8_t_of_elem (a: ptr) (#p: perm) (#x: I8.t)
  requires elem_pts_to int8_t_repr a p x
  ensures  int8_t_pts_to a p x


ghost fn int8_t_to_elem (a: ptr) (#p: perm) (#x: I8.t)
  requires int8_t_pts_to a p x
  ensures  elem_pts_to int8_t_repr a p x


ghost fn int16_t_of_elem (a: ptr) (#p: perm) (#x: I16.t)
  requires elem_pts_to int16_t_repr a p x
  ensures  int16_t_pts_to a p x


ghost fn int16_t_to_elem (a: ptr) (#p: perm) (#x: I16.t)
  requires int16_t_pts_to a p x
  ensures  elem_pts_to int16_t_repr a p x


ghost fn int32_t_of_elem (a: ptr) (#p: perm) (#x: I32.t)
  requires elem_pts_to int32_t_repr a p x
  ensures  int32_t_pts_to a p x


ghost fn int32_t_to_elem (a: ptr) (#p: perm) (#x: I32.t)
  requires int32_t_pts_to a p x
  ensures  elem_pts_to int32_t_repr a p x


ghost fn int64_t_of_elem (a: ptr) (#p: perm) (#x: I64.t)
  requires elem_pts_to int64_t_repr a p x
  ensures  int64_t_pts_to a p x


ghost fn int64_t_to_elem (a: ptr) (#p: perm) (#x: I64.t)
  requires int64_t_pts_to a p x
  ensures  elem_pts_to int64_t_repr a p x


ghost fn uint16_t_of_elem (a: ptr) (#p: perm) (#x: U16.t)
  requires elem_pts_to uint16_t_repr a p x
  ensures  uint16_t_pts_to a p x


ghost fn uint16_t_to_elem (a: ptr) (#p: perm) (#x: U16.t)
  requires uint16_t_pts_to a p x
  ensures  elem_pts_to uint16_t_repr a p x


ghost fn uint64_t_of_elem (a: ptr) (#p: perm) (#x: U64.t)
  requires elem_pts_to uint64_t_repr a p x
  ensures  uint64_t_pts_to a p x


ghost fn uint64_t_to_elem (a: ptr) (#p: perm) (#x: U64.t)
  requires uint64_t_pts_to a p x
  ensures  elem_pts_to uint64_t_repr a p x


ghost fn size_t_of_elem (a: ptr) (#p: perm) (#x: SZ.t)
  requires elem_pts_to size_t_repr a p x
  ensures  size_t_pts_to a p x


ghost fn size_t_to_elem (a: ptr) (#p: perm) (#x: SZ.t)
  requires size_t_pts_to a p x
  ensures  elem_pts_to size_t_repr a p x




(* ---------------------------------------------------------------------------
   Uniform length lemmas

   Every scalar already says how long its representation is, but it says so in
   whichever lemma happened to be convenient: some carry it alongside a
   provenance fact, `uint8_t`/`uint32_t`/`ptr` have a dedicated one, and a
   generated aggregate states it as the first conjunct of its `_repr`. A
   generated struct has to join its fields' byte ranges in offset order, and
   `mem_join` wants each length as a side condition, so the generator needs one
   name that works for every field type. These supply the missing ones.
   --------------------------------------------------------------------------- *)

let bool_t_repr_len (x: bool) (b: bytes)
  : Lemma (requires bool_t_repr x b) (ensures len b == SZ.v bool_t_sizeof)
  = bool_t_repr_no_prov x b

let int8_t_repr_len (x: I8.t) (b: bytes)
  : Lemma (requires int8_t_repr x b) (ensures len b == SZ.v int8_t_sizeof)
  = int8_t_repr_no_prov x b

let int16_t_repr_len (x: I16.t) (b: bytes)
  : Lemma (requires int16_t_repr x b) (ensures len b == SZ.v int16_t_sizeof)
  = int16_t_repr_no_prov x b

let int32_t_repr_len (x: I32.t) (b: bytes)
  : Lemma (requires int32_t_repr x b) (ensures len b == SZ.v int32_t_sizeof)
  = int32_t_repr_no_prov x b

let int64_t_repr_len (x: I64.t) (b: bytes)
  : Lemma (requires int64_t_repr x b) (ensures len b == SZ.v int64_t_sizeof)
  = int64_t_repr_no_prov x b

let uint16_t_repr_len (x: U16.t) (b: bytes)
  : Lemma (requires uint16_t_repr x b) (ensures len b == SZ.v uint16_t_sizeof)
  = uint16_t_repr_no_prov x b

let uint64_t_repr_len (x: U64.t) (b: bytes)
  : Lemma (requires uint64_t_repr x b) (ensures len b == SZ.v uint64_t_sizeof)
  = uint64_t_repr_no_prov x b

let size_t_repr_len (x: SZ.t) (b: bytes)
  : Lemma (requires size_t_repr x b) (ensures len b == SZ.v size_t_sizeof)
  = size_t_repr_no_prov x b

(* ---------------------------------------------------------------------------
   Floating point

   A C floating-point value is an object like any other: it has a size, an
   alignment and an object representation. `Pulse.Lib.C.Palow.Float` supplies
   the one thing F* does not already say -- the injective map from a value to
   its bits -- and these two blocks are then the same construction as every
   scalar above, with `float32_bits` where a signed integer has
   `Encoding.to_bits`.
   --------------------------------------------------------------------------- *)

(* ------------------------------ float32_t ------------------------------ *)

let float32_t_sizeof : SZ.t = 4sz
let float32_t_alignof : SZ.t = 4sz

let float32_t_repr (x: float32) (b: bytes) : prop =
  b == encode (SZ.v float32_t_sizeof) None (float32_bits x)

val float32_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: float32) : slprop


val float32_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop


val float32_t_repr_no_prov (x: float32) (b: bytes)
  : Lemma (requires float32_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v float32_t_sizeof)


val float32_t_repr_injective (x y: float32) (b: bytes)
  : Lemma (requires float32_t_repr x b /\ float32_t_repr y b)
          (ensures  x == y)


ghost fn float32_t_pts_to_not_null (a: ptr) (#p: perm) (#x: float32)
  preserves float32_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


(* Unwritten storage is still storage: it occupies float32_t_sizeof bytes at a real
   address, so the pointer to it cannot be NULL. This is what makes an `_out`
   parameter refined to be NULL vacuous rather than merely unprovable. *)
ghost fn float32_t_pts_to_uninit_not_null (a: ptr)
  preserves float32_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


[@@allow_ambiguous]
ghost fn float32_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: float32)
  preserves float32_t_pts_to a p1 x
  preserves float32_t_pts_to a p2 y
  ensures   pure (x == y)


ghost fn float32_t_share (a: ptr) (#p: perm) (#x: float32)
  requires float32_t_pts_to a p x
  ensures  float32_t_pts_to a (p /. 2.0R) x ** float32_t_pts_to a (p /. 2.0R) x


[@@allow_ambiguous]
ghost fn float32_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: float32)
  requires float32_t_pts_to a p1 x ** float32_t_pts_to a p2 y
  ensures  float32_t_pts_to a (p1 +. p2) x ** pure (x == y)


ghost fn float32_t_reveal (a: ptr) (#p: perm) (#x: float32)
  requires float32_t_pts_to a p x
  ensures  exists* b. mem_pts_to a p b ** pure (float32_t_repr x b)


ghost fn float32_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: float32)
  requires mem_pts_to a p b
  requires pure (float32_t_repr x b)
  ensures  float32_t_pts_to a p x


ghost fn float32_t_forget (a: ptr) (#x: float32)
  requires float32_t_pts_to a 1.0R x
  ensures  float32_t_pts_to_uninit a


ghost fn float32_t_claim (a: ptr) (#b: bytes) (x: float32)
  requires mem_pts_to a 1.0R b
  requires pure (float32_t_repr x b)
  ensures  float32_t_pts_to a 1.0R x

(* Raw storage of the right size is write-only ownership at this type, and back
   again: the two directions an allocation and a deallocation take. *)
ghost fn float32_t_claim_uninit (a: ptr) (#b: bytes)
  requires mem_pts_to a 1.0R b
  requires pure (len b == SZ.v float32_t_sizeof)
  ensures  float32_t_pts_to_uninit a


ghost fn float32_t_reveal_uninit (a: ptr)
  requires float32_t_pts_to_uninit a
  ensures  exists* b. mem_pts_to a 1.0R b ** pure (len b == SZ.v float32_t_sizeof)



(* ------------------------------ float64_t ------------------------------ *)

let float64_t_sizeof : SZ.t = 8sz
let float64_t_alignof : SZ.t = 8sz

let float64_t_repr (x: float64) (b: bytes) : prop =
  b == encode (SZ.v float64_t_sizeof) None (float64_bits x)

val float64_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: float64) : slprop


val float64_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop


val float64_t_repr_no_prov (x: float64) (b: bytes)
  : Lemma (requires float64_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v float64_t_sizeof)


val float64_t_repr_injective (x y: float64) (b: bytes)
  : Lemma (requires float64_t_repr x b /\ float64_t_repr y b)
          (ensures  x == y)


ghost fn float64_t_pts_to_not_null (a: ptr) (#p: perm) (#x: float64)
  preserves float64_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


(* Unwritten storage is still storage: it occupies float64_t_sizeof bytes at a real
   address, so the pointer to it cannot be NULL. This is what makes an `_out`
   parameter refined to be NULL vacuous rather than merely unprovable. *)
ghost fn float64_t_pts_to_uninit_not_null (a: ptr)
  preserves float64_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


[@@allow_ambiguous]
ghost fn float64_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: float64)
  preserves float64_t_pts_to a p1 x
  preserves float64_t_pts_to a p2 y
  ensures   pure (x == y)


ghost fn float64_t_share (a: ptr) (#p: perm) (#x: float64)
  requires float64_t_pts_to a p x
  ensures  float64_t_pts_to a (p /. 2.0R) x ** float64_t_pts_to a (p /. 2.0R) x


[@@allow_ambiguous]
ghost fn float64_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: float64)
  requires float64_t_pts_to a p1 x ** float64_t_pts_to a p2 y
  ensures  float64_t_pts_to a (p1 +. p2) x ** pure (x == y)


ghost fn float64_t_reveal (a: ptr) (#p: perm) (#x: float64)
  requires float64_t_pts_to a p x
  ensures  exists* b. mem_pts_to a p b ** pure (float64_t_repr x b)


ghost fn float64_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: float64)
  requires mem_pts_to a p b
  requires pure (float64_t_repr x b)
  ensures  float64_t_pts_to a p x


ghost fn float64_t_forget (a: ptr) (#x: float64)
  requires float64_t_pts_to a 1.0R x
  ensures  float64_t_pts_to_uninit a


ghost fn float64_t_claim (a: ptr) (#b: bytes) (x: float64)
  requires mem_pts_to a 1.0R b
  requires pure (float64_t_repr x b)
  ensures  float64_t_pts_to a 1.0R x

(* Raw storage of the right size is write-only ownership at this type, and back
   again: the two directions an allocation and a deallocation take. *)
ghost fn float64_t_claim_uninit (a: ptr) (#b: bytes)
  requires mem_pts_to a 1.0R b
  requires pure (len b == SZ.v float64_t_sizeof)
  ensures  float64_t_pts_to_uninit a


ghost fn float64_t_reveal_uninit (a: ptr)
  requires float64_t_pts_to_uninit a
  ensures  exists* b. mem_pts_to a 1.0R b ** pure (len b == SZ.v float64_t_sizeof)


ghost fn float32_t_of_elem (a: ptr) (#p: perm) (#x: float32)
  requires elem_pts_to float32_t_repr a p x
  ensures  float32_t_pts_to a p x


ghost fn float32_t_to_elem (a: ptr) (#p: perm) (#x: float32)
  requires float32_t_pts_to a p x
  ensures  elem_pts_to float32_t_repr a p x


let float32_t_repr_len (x: float32) (b: bytes)
  : Lemma (requires float32_t_repr x b) (ensures len b == SZ.v float32_t_sizeof)
  = float32_t_repr_no_prov x b


ghost fn float64_t_of_elem (a: ptr) (#p: perm) (#x: float64)
  requires elem_pts_to float64_t_repr a p x
  ensures  float64_t_pts_to a p x


ghost fn float64_t_to_elem (a: ptr) (#p: perm) (#x: float64)
  requires float64_t_pts_to a p x
  ensures  elem_pts_to float64_t_repr a p x


let float64_t_repr_len (x: float64) (b: bytes)
  : Lemma (requires float64_t_repr x b) (ensures len b == SZ.v float64_t_sizeof)
  = float64_t_repr_no_prov x b
