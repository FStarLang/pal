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
open Pulse.Lib.C.Palow.Scalar

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

