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

module ET = Pulse.Lib.C.Palow.Etype
module T = Pulse.Lib.C.Palow.Effective.Typed
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



let bool_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: bool) : slprop =
  T.value bool_t_ctype bool_t_repr bool_t_alignof a p x

let bool_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop =
  T.storage bool_t_ctype bool_t_alignof a

let bool_t_repr_no_prov (x: bool) (b: bytes)
  : Lemma (requires bool_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v bool_t_sizeof)
  = ()

let bool_t_repr_injective (x y: bool) (b: bytes)
  : Lemma (requires bool_t_repr x b /\ bool_t_repr y b)
          (ensures  x == y)
  = assert_norm (pow2 (8 * 1) == pow2 8);
    encode_injective (SZ.v bool_t_sizeof) None (if x then 1 else 0) (if y then 1 else 0)

ghost fn bool_t_pts_to_not_null (a: ptr) (#p: perm) (#x: bool)
  preserves bool_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold bool_t_pts_to a p x;
  T.not_null bool_t_ctype bool_t_repr bool_t_alignof a;
  fold bool_t_pts_to a p x;
}

ghost fn bool_t_pts_to_uninit_not_null (a: ptr)
  preserves bool_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold bool_t_pts_to_uninit a;
  T.storage_not_null bool_t_ctype bool_t_alignof a;
  fold bool_t_pts_to_uninit a;
}

[@@allow_ambiguous]
ghost fn bool_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: bool)
  preserves bool_t_pts_to a p1 x
  preserves bool_t_pts_to a p2 y
  ensures   pure (x == y)
{
  unfold bool_t_pts_to a p1 x;
  unfold bool_t_pts_to a p2 y;
  T.agree bool_t_ctype bool_t_repr bool_t_alignof bool_t_repr_injective a;
  fold bool_t_pts_to a p1 x;
  fold bool_t_pts_to a p2 y;
}

ghost fn bool_t_share (a: ptr) (#p: perm) (#x: bool)
  requires bool_t_pts_to a p x
  ensures  bool_t_pts_to a (p /. 2.0R) x ** bool_t_pts_to a (p /. 2.0R) x
{
  unfold bool_t_pts_to a p x;
  T.share bool_t_ctype bool_t_repr bool_t_alignof a;
  fold bool_t_pts_to a (p /. 2.0R) x;
  fold bool_t_pts_to a (p /. 2.0R) x;
}

[@@allow_ambiguous]
ghost fn bool_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: bool)
  requires bool_t_pts_to a p1 x ** bool_t_pts_to a p2 y
  ensures  bool_t_pts_to a (p1 +. p2) x ** pure (x == y)
{
  unfold bool_t_pts_to a p1 x;
  unfold bool_t_pts_to a p2 y;
  T.gather bool_t_ctype bool_t_repr bool_t_alignof bool_t_repr_injective a;
  fold bool_t_pts_to a (p1 +. p2) x;
}

ghost fn bool_t_reveal (a: ptr) (#p: perm) (#x: bool)
  requires bool_t_pts_to a p x
  ensures  exists* b e. mem_pts_to_at a p b e ** pure (ET.elen e == len b /\ ET.read_ok e bool_t_ctype /\ bool_t_repr x b /\ aligned a bool_t_alignof)
{
  unfold bool_t_pts_to a p x;
  T.reveal_value bool_t_ctype bool_t_repr bool_t_alignof a;
}

ghost fn bool_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: bool) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (bool_t_repr x b)
  requires pure (aligned a bool_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e bool_t_ctype)
  ensures  bool_t_pts_to a p x
{
  bool_t_repr_no_prov x b;
  T.claim bool_t_ctype bool_t_repr bool_t_alignof a #p #x #b #e;
  fold bool_t_pts_to a p x;
}

ghost fn bool_t_forget (a: ptr) (#x: bool)
  requires bool_t_pts_to a 1.0R x
  ensures  bool_t_pts_to_uninit a
{
  unfold bool_t_pts_to a 1.0R x;
  T.forget bool_t_ctype bool_t_repr bool_t_alignof a;
  fold bool_t_pts_to_uninit a;
}

ghost fn bool_t_claim (a: ptr) (#b: bytes) (x: bool) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (bool_t_repr x b)
  requires pure (aligned a bool_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e bool_t_ctype)
  ensures  bool_t_pts_to a 1.0R x
{
  bool_t_repr_no_prov x b;
  T.claim bool_t_ctype bool_t_repr bool_t_alignof a #1.0R #x #b #e;
  fold bool_t_pts_to a 1.0R x;
}

ghost fn bool_t_claim_uninit (a: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v bool_t_sizeof /\ aligned a bool_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e bool_t_ctype)
  ensures  bool_t_pts_to_uninit a
{
  T.claim_storage bool_t_ctype bool_t_alignof a;
  fold bool_t_pts_to_uninit a;
}

ghost fn bool_t_reveal_uninit (a: ptr)
  requires bool_t_pts_to_uninit a
  ensures  exists* b e. mem_pts_to_at a 1.0R b e ** pure (ET.elen e == len b /\ ET.read_ok e bool_t_ctype /\ len b == SZ.v bool_t_sizeof /\ aligned a bool_t_alignof)
{
  unfold bool_t_pts_to_uninit a;
  T.reveal_storage bool_t_ctype bool_t_alignof a;
}

(* ------------------------------- int8_t ------------------------------- *)



let int8_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: I8.t) : slprop =
  T.value int8_t_ctype int8_t_repr int8_t_alignof a p x

let int8_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop =
  T.storage int8_t_ctype int8_t_alignof a

let int8_t_repr_no_prov (x: I8.t) (b: bytes)
  : Lemma (requires int8_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v int8_t_sizeof)
  = ()

let int8_t_repr_injective (x y: I8.t) (b: bytes)
  : Lemma (requires int8_t_repr x b /\ int8_t_repr y b)
          (ensures  x == y)
  = assert_norm (pow2 (8 * 1) == pow2 8);
    encode_injective (SZ.v int8_t_sizeof) None (to_bits 8 (I8.v x)) (to_bits 8 (I8.v y));
    to_bits_injective 8 (I8.v x) (I8.v y)

ghost fn int8_t_pts_to_not_null (a: ptr) (#p: perm) (#x: I8.t)
  preserves int8_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold int8_t_pts_to a p x;
  T.not_null int8_t_ctype int8_t_repr int8_t_alignof a;
  fold int8_t_pts_to a p x;
}

ghost fn int8_t_pts_to_uninit_not_null (a: ptr)
  preserves int8_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold int8_t_pts_to_uninit a;
  T.storage_not_null int8_t_ctype int8_t_alignof a;
  fold int8_t_pts_to_uninit a;
}

[@@allow_ambiguous]
ghost fn int8_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: I8.t)
  preserves int8_t_pts_to a p1 x
  preserves int8_t_pts_to a p2 y
  ensures   pure (x == y)
{
  unfold int8_t_pts_to a p1 x;
  unfold int8_t_pts_to a p2 y;
  T.agree int8_t_ctype int8_t_repr int8_t_alignof int8_t_repr_injective a;
  fold int8_t_pts_to a p1 x;
  fold int8_t_pts_to a p2 y;
}

ghost fn int8_t_share (a: ptr) (#p: perm) (#x: I8.t)
  requires int8_t_pts_to a p x
  ensures  int8_t_pts_to a (p /. 2.0R) x ** int8_t_pts_to a (p /. 2.0R) x
{
  unfold int8_t_pts_to a p x;
  T.share int8_t_ctype int8_t_repr int8_t_alignof a;
  fold int8_t_pts_to a (p /. 2.0R) x;
  fold int8_t_pts_to a (p /. 2.0R) x;
}

[@@allow_ambiguous]
ghost fn int8_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: I8.t)
  requires int8_t_pts_to a p1 x ** int8_t_pts_to a p2 y
  ensures  int8_t_pts_to a (p1 +. p2) x ** pure (x == y)
{
  unfold int8_t_pts_to a p1 x;
  unfold int8_t_pts_to a p2 y;
  T.gather int8_t_ctype int8_t_repr int8_t_alignof int8_t_repr_injective a;
  fold int8_t_pts_to a (p1 +. p2) x;
}

ghost fn int8_t_reveal (a: ptr) (#p: perm) (#x: I8.t)
  requires int8_t_pts_to a p x
  ensures  exists* b e. mem_pts_to_at a p b e ** pure (ET.elen e == len b /\ ET.read_ok e int8_t_ctype /\ int8_t_repr x b /\ aligned a int8_t_alignof)
{
  unfold int8_t_pts_to a p x;
  T.reveal_value int8_t_ctype int8_t_repr int8_t_alignof a;
}

ghost fn int8_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: I8.t) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (int8_t_repr x b)
  requires pure (aligned a int8_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e int8_t_ctype)
  ensures  int8_t_pts_to a p x
{
  int8_t_repr_no_prov x b;
  T.claim int8_t_ctype int8_t_repr int8_t_alignof a #p #x #b #e;
  fold int8_t_pts_to a p x;
}

ghost fn int8_t_forget (a: ptr) (#x: I8.t)
  requires int8_t_pts_to a 1.0R x
  ensures  int8_t_pts_to_uninit a
{
  unfold int8_t_pts_to a 1.0R x;
  T.forget int8_t_ctype int8_t_repr int8_t_alignof a;
  fold int8_t_pts_to_uninit a;
}

ghost fn int8_t_claim (a: ptr) (#b: bytes) (x: I8.t) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (int8_t_repr x b)
  requires pure (aligned a int8_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e int8_t_ctype)
  ensures  int8_t_pts_to a 1.0R x
{
  int8_t_repr_no_prov x b;
  T.claim int8_t_ctype int8_t_repr int8_t_alignof a #1.0R #x #b #e;
  fold int8_t_pts_to a 1.0R x;
}

ghost fn int8_t_claim_uninit (a: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v int8_t_sizeof /\ aligned a int8_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e int8_t_ctype)
  ensures  int8_t_pts_to_uninit a
{
  T.claim_storage int8_t_ctype int8_t_alignof a;
  fold int8_t_pts_to_uninit a;
}

ghost fn int8_t_reveal_uninit (a: ptr)
  requires int8_t_pts_to_uninit a
  ensures  exists* b e. mem_pts_to_at a 1.0R b e ** pure (ET.elen e == len b /\ ET.read_ok e int8_t_ctype /\ len b == SZ.v int8_t_sizeof /\ aligned a int8_t_alignof)
{
  unfold int8_t_pts_to_uninit a;
  T.reveal_storage int8_t_ctype int8_t_alignof a;
}

(* ------------------------------- int16_t ------------------------------- *)



let int16_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: I16.t) : slprop =
  T.value int16_t_ctype int16_t_repr int16_t_alignof a p x

let int16_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop =
  T.storage int16_t_ctype int16_t_alignof a

let int16_t_repr_no_prov (x: I16.t) (b: bytes)
  : Lemma (requires int16_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v int16_t_sizeof)
  = ()

let int16_t_repr_injective (x y: I16.t) (b: bytes)
  : Lemma (requires int16_t_repr x b /\ int16_t_repr y b)
          (ensures  x == y)
  = assert_norm (pow2 (8 * 2) == pow2 16);
    encode_injective (SZ.v int16_t_sizeof) None (to_bits 16 (I16.v x)) (to_bits 16 (I16.v y));
    to_bits_injective 16 (I16.v x) (I16.v y)

ghost fn int16_t_pts_to_not_null (a: ptr) (#p: perm) (#x: I16.t)
  preserves int16_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold int16_t_pts_to a p x;
  T.not_null int16_t_ctype int16_t_repr int16_t_alignof a;
  fold int16_t_pts_to a p x;
}

ghost fn int16_t_pts_to_uninit_not_null (a: ptr)
  preserves int16_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold int16_t_pts_to_uninit a;
  T.storage_not_null int16_t_ctype int16_t_alignof a;
  fold int16_t_pts_to_uninit a;
}

[@@allow_ambiguous]
ghost fn int16_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: I16.t)
  preserves int16_t_pts_to a p1 x
  preserves int16_t_pts_to a p2 y
  ensures   pure (x == y)
{
  unfold int16_t_pts_to a p1 x;
  unfold int16_t_pts_to a p2 y;
  T.agree int16_t_ctype int16_t_repr int16_t_alignof int16_t_repr_injective a;
  fold int16_t_pts_to a p1 x;
  fold int16_t_pts_to a p2 y;
}

ghost fn int16_t_share (a: ptr) (#p: perm) (#x: I16.t)
  requires int16_t_pts_to a p x
  ensures  int16_t_pts_to a (p /. 2.0R) x ** int16_t_pts_to a (p /. 2.0R) x
{
  unfold int16_t_pts_to a p x;
  T.share int16_t_ctype int16_t_repr int16_t_alignof a;
  fold int16_t_pts_to a (p /. 2.0R) x;
  fold int16_t_pts_to a (p /. 2.0R) x;
}

[@@allow_ambiguous]
ghost fn int16_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: I16.t)
  requires int16_t_pts_to a p1 x ** int16_t_pts_to a p2 y
  ensures  int16_t_pts_to a (p1 +. p2) x ** pure (x == y)
{
  unfold int16_t_pts_to a p1 x;
  unfold int16_t_pts_to a p2 y;
  T.gather int16_t_ctype int16_t_repr int16_t_alignof int16_t_repr_injective a;
  fold int16_t_pts_to a (p1 +. p2) x;
}

ghost fn int16_t_reveal (a: ptr) (#p: perm) (#x: I16.t)
  requires int16_t_pts_to a p x
  ensures  exists* b e. mem_pts_to_at a p b e ** pure (ET.elen e == len b /\ ET.read_ok e int16_t_ctype /\ int16_t_repr x b /\ aligned a int16_t_alignof)
{
  unfold int16_t_pts_to a p x;
  T.reveal_value int16_t_ctype int16_t_repr int16_t_alignof a;
}

ghost fn int16_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: I16.t) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (int16_t_repr x b)
  requires pure (aligned a int16_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e int16_t_ctype)
  ensures  int16_t_pts_to a p x
{
  int16_t_repr_no_prov x b;
  T.claim int16_t_ctype int16_t_repr int16_t_alignof a #p #x #b #e;
  fold int16_t_pts_to a p x;
}

ghost fn int16_t_forget (a: ptr) (#x: I16.t)
  requires int16_t_pts_to a 1.0R x
  ensures  int16_t_pts_to_uninit a
{
  unfold int16_t_pts_to a 1.0R x;
  T.forget int16_t_ctype int16_t_repr int16_t_alignof a;
  fold int16_t_pts_to_uninit a;
}

ghost fn int16_t_claim (a: ptr) (#b: bytes) (x: I16.t) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (int16_t_repr x b)
  requires pure (aligned a int16_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e int16_t_ctype)
  ensures  int16_t_pts_to a 1.0R x
{
  int16_t_repr_no_prov x b;
  T.claim int16_t_ctype int16_t_repr int16_t_alignof a #1.0R #x #b #e;
  fold int16_t_pts_to a 1.0R x;
}

ghost fn int16_t_claim_uninit (a: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v int16_t_sizeof /\ aligned a int16_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e int16_t_ctype)
  ensures  int16_t_pts_to_uninit a
{
  T.claim_storage int16_t_ctype int16_t_alignof a;
  fold int16_t_pts_to_uninit a;
}

ghost fn int16_t_reveal_uninit (a: ptr)
  requires int16_t_pts_to_uninit a
  ensures  exists* b e. mem_pts_to_at a 1.0R b e ** pure (ET.elen e == len b /\ ET.read_ok e int16_t_ctype /\ len b == SZ.v int16_t_sizeof /\ aligned a int16_t_alignof)
{
  unfold int16_t_pts_to_uninit a;
  T.reveal_storage int16_t_ctype int16_t_alignof a;
}

(* ------------------------------- int32_t ------------------------------- *)



let int32_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: I32.t) : slprop =
  T.value int32_t_ctype int32_t_repr int32_t_alignof a p x

let int32_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop =
  T.storage int32_t_ctype int32_t_alignof a

let int32_t_repr_no_prov (x: I32.t) (b: bytes)
  : Lemma (requires int32_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v int32_t_sizeof)
  = ()

let int32_t_repr_injective (x y: I32.t) (b: bytes)
  : Lemma (requires int32_t_repr x b /\ int32_t_repr y b)
          (ensures  x == y)
  = assert_norm (pow2 (8 * 4) == pow2 32);
    encode_injective (SZ.v int32_t_sizeof) None (to_bits 32 (I32.v x)) (to_bits 32 (I32.v y));
    to_bits_injective 32 (I32.v x) (I32.v y)

ghost fn int32_t_pts_to_not_null (a: ptr) (#p: perm) (#x: I32.t)
  preserves int32_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold int32_t_pts_to a p x;
  T.not_null int32_t_ctype int32_t_repr int32_t_alignof a;
  fold int32_t_pts_to a p x;
}

ghost fn int32_t_pts_to_uninit_not_null (a: ptr)
  preserves int32_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold int32_t_pts_to_uninit a;
  T.storage_not_null int32_t_ctype int32_t_alignof a;
  fold int32_t_pts_to_uninit a;
}

[@@allow_ambiguous]
ghost fn int32_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: I32.t)
  preserves int32_t_pts_to a p1 x
  preserves int32_t_pts_to a p2 y
  ensures   pure (x == y)
{
  unfold int32_t_pts_to a p1 x;
  unfold int32_t_pts_to a p2 y;
  T.agree int32_t_ctype int32_t_repr int32_t_alignof int32_t_repr_injective a;
  fold int32_t_pts_to a p1 x;
  fold int32_t_pts_to a p2 y;
}

ghost fn int32_t_share (a: ptr) (#p: perm) (#x: I32.t)
  requires int32_t_pts_to a p x
  ensures  int32_t_pts_to a (p /. 2.0R) x ** int32_t_pts_to a (p /. 2.0R) x
{
  unfold int32_t_pts_to a p x;
  T.share int32_t_ctype int32_t_repr int32_t_alignof a;
  fold int32_t_pts_to a (p /. 2.0R) x;
  fold int32_t_pts_to a (p /. 2.0R) x;
}

[@@allow_ambiguous]
ghost fn int32_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: I32.t)
  requires int32_t_pts_to a p1 x ** int32_t_pts_to a p2 y
  ensures  int32_t_pts_to a (p1 +. p2) x ** pure (x == y)
{
  unfold int32_t_pts_to a p1 x;
  unfold int32_t_pts_to a p2 y;
  T.gather int32_t_ctype int32_t_repr int32_t_alignof int32_t_repr_injective a;
  fold int32_t_pts_to a (p1 +. p2) x;
}

ghost fn int32_t_reveal (a: ptr) (#p: perm) (#x: I32.t)
  requires int32_t_pts_to a p x
  ensures  exists* b e. mem_pts_to_at a p b e ** pure (ET.elen e == len b /\ ET.read_ok e int32_t_ctype /\ int32_t_repr x b /\ aligned a int32_t_alignof)
{
  unfold int32_t_pts_to a p x;
  T.reveal_value int32_t_ctype int32_t_repr int32_t_alignof a;
}

ghost fn int32_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: I32.t) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (int32_t_repr x b)
  requires pure (aligned a int32_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e int32_t_ctype)
  ensures  int32_t_pts_to a p x
{
  int32_t_repr_no_prov x b;
  T.claim int32_t_ctype int32_t_repr int32_t_alignof a #p #x #b #e;
  fold int32_t_pts_to a p x;
}

ghost fn int32_t_forget (a: ptr) (#x: I32.t)
  requires int32_t_pts_to a 1.0R x
  ensures  int32_t_pts_to_uninit a
{
  unfold int32_t_pts_to a 1.0R x;
  T.forget int32_t_ctype int32_t_repr int32_t_alignof a;
  fold int32_t_pts_to_uninit a;
}

ghost fn int32_t_claim (a: ptr) (#b: bytes) (x: I32.t) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (int32_t_repr x b)
  requires pure (aligned a int32_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e int32_t_ctype)
  ensures  int32_t_pts_to a 1.0R x
{
  int32_t_repr_no_prov x b;
  T.claim int32_t_ctype int32_t_repr int32_t_alignof a #1.0R #x #b #e;
  fold int32_t_pts_to a 1.0R x;
}

ghost fn int32_t_claim_uninit (a: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v int32_t_sizeof /\ aligned a int32_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e int32_t_ctype)
  ensures  int32_t_pts_to_uninit a
{
  T.claim_storage int32_t_ctype int32_t_alignof a;
  fold int32_t_pts_to_uninit a;
}

ghost fn int32_t_reveal_uninit (a: ptr)
  requires int32_t_pts_to_uninit a
  ensures  exists* b e. mem_pts_to_at a 1.0R b e ** pure (ET.elen e == len b /\ ET.read_ok e int32_t_ctype /\ len b == SZ.v int32_t_sizeof /\ aligned a int32_t_alignof)
{
  unfold int32_t_pts_to_uninit a;
  T.reveal_storage int32_t_ctype int32_t_alignof a;
}

(* ------------------------------- int64_t ------------------------------- *)



let int64_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: I64.t) : slprop =
  T.value int64_t_ctype int64_t_repr int64_t_alignof a p x

let int64_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop =
  T.storage int64_t_ctype int64_t_alignof a

let int64_t_repr_no_prov (x: I64.t) (b: bytes)
  : Lemma (requires int64_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v int64_t_sizeof)
  = ()

let int64_t_repr_injective (x y: I64.t) (b: bytes)
  : Lemma (requires int64_t_repr x b /\ int64_t_repr y b)
          (ensures  x == y)
  = assert_norm (pow2 (8 * 8) == pow2 64);
    encode_injective (SZ.v int64_t_sizeof) None (to_bits 64 (I64.v x)) (to_bits 64 (I64.v y));
    to_bits_injective 64 (I64.v x) (I64.v y)

ghost fn int64_t_pts_to_not_null (a: ptr) (#p: perm) (#x: I64.t)
  preserves int64_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold int64_t_pts_to a p x;
  T.not_null int64_t_ctype int64_t_repr int64_t_alignof a;
  fold int64_t_pts_to a p x;
}

ghost fn int64_t_pts_to_uninit_not_null (a: ptr)
  preserves int64_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold int64_t_pts_to_uninit a;
  T.storage_not_null int64_t_ctype int64_t_alignof a;
  fold int64_t_pts_to_uninit a;
}

[@@allow_ambiguous]
ghost fn int64_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: I64.t)
  preserves int64_t_pts_to a p1 x
  preserves int64_t_pts_to a p2 y
  ensures   pure (x == y)
{
  unfold int64_t_pts_to a p1 x;
  unfold int64_t_pts_to a p2 y;
  T.agree int64_t_ctype int64_t_repr int64_t_alignof int64_t_repr_injective a;
  fold int64_t_pts_to a p1 x;
  fold int64_t_pts_to a p2 y;
}

ghost fn int64_t_share (a: ptr) (#p: perm) (#x: I64.t)
  requires int64_t_pts_to a p x
  ensures  int64_t_pts_to a (p /. 2.0R) x ** int64_t_pts_to a (p /. 2.0R) x
{
  unfold int64_t_pts_to a p x;
  T.share int64_t_ctype int64_t_repr int64_t_alignof a;
  fold int64_t_pts_to a (p /. 2.0R) x;
  fold int64_t_pts_to a (p /. 2.0R) x;
}

[@@allow_ambiguous]
ghost fn int64_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: I64.t)
  requires int64_t_pts_to a p1 x ** int64_t_pts_to a p2 y
  ensures  int64_t_pts_to a (p1 +. p2) x ** pure (x == y)
{
  unfold int64_t_pts_to a p1 x;
  unfold int64_t_pts_to a p2 y;
  T.gather int64_t_ctype int64_t_repr int64_t_alignof int64_t_repr_injective a;
  fold int64_t_pts_to a (p1 +. p2) x;
}

ghost fn int64_t_reveal (a: ptr) (#p: perm) (#x: I64.t)
  requires int64_t_pts_to a p x
  ensures  exists* b e. mem_pts_to_at a p b e ** pure (ET.elen e == len b /\ ET.read_ok e int64_t_ctype /\ int64_t_repr x b /\ aligned a int64_t_alignof)
{
  unfold int64_t_pts_to a p x;
  T.reveal_value int64_t_ctype int64_t_repr int64_t_alignof a;
}

ghost fn int64_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: I64.t) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (int64_t_repr x b)
  requires pure (aligned a int64_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e int64_t_ctype)
  ensures  int64_t_pts_to a p x
{
  int64_t_repr_no_prov x b;
  T.claim int64_t_ctype int64_t_repr int64_t_alignof a #p #x #b #e;
  fold int64_t_pts_to a p x;
}

ghost fn int64_t_forget (a: ptr) (#x: I64.t)
  requires int64_t_pts_to a 1.0R x
  ensures  int64_t_pts_to_uninit a
{
  unfold int64_t_pts_to a 1.0R x;
  T.forget int64_t_ctype int64_t_repr int64_t_alignof a;
  fold int64_t_pts_to_uninit a;
}

ghost fn int64_t_claim (a: ptr) (#b: bytes) (x: I64.t) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (int64_t_repr x b)
  requires pure (aligned a int64_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e int64_t_ctype)
  ensures  int64_t_pts_to a 1.0R x
{
  int64_t_repr_no_prov x b;
  T.claim int64_t_ctype int64_t_repr int64_t_alignof a #1.0R #x #b #e;
  fold int64_t_pts_to a 1.0R x;
}

ghost fn int64_t_claim_uninit (a: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v int64_t_sizeof /\ aligned a int64_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e int64_t_ctype)
  ensures  int64_t_pts_to_uninit a
{
  T.claim_storage int64_t_ctype int64_t_alignof a;
  fold int64_t_pts_to_uninit a;
}

ghost fn int64_t_reveal_uninit (a: ptr)
  requires int64_t_pts_to_uninit a
  ensures  exists* b e. mem_pts_to_at a 1.0R b e ** pure (ET.elen e == len b /\ ET.read_ok e int64_t_ctype /\ len b == SZ.v int64_t_sizeof /\ aligned a int64_t_alignof)
{
  unfold int64_t_pts_to_uninit a;
  T.reveal_storage int64_t_ctype int64_t_alignof a;
}

(* ------------------------------- uint16_t ------------------------------- *)



let uint16_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: U16.t) : slprop =
  T.value uint16_t_ctype uint16_t_repr uint16_t_alignof a p x

let uint16_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop =
  T.storage uint16_t_ctype uint16_t_alignof a

let uint16_t_repr_no_prov (x: U16.t) (b: bytes)
  : Lemma (requires uint16_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v uint16_t_sizeof)
  = ()

let uint16_t_repr_injective (x y: U16.t) (b: bytes)
  : Lemma (requires uint16_t_repr x b /\ uint16_t_repr y b)
          (ensures  x == y)
  = assert_norm (pow2 (8 * 2) == pow2 16);
    encode_injective (SZ.v uint16_t_sizeof) None (U16.v x) (U16.v y)

ghost fn uint16_t_pts_to_not_null (a: ptr) (#p: perm) (#x: U16.t)
  preserves uint16_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold uint16_t_pts_to a p x;
  T.not_null uint16_t_ctype uint16_t_repr uint16_t_alignof a;
  fold uint16_t_pts_to a p x;
}

ghost fn uint16_t_pts_to_uninit_not_null (a: ptr)
  preserves uint16_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold uint16_t_pts_to_uninit a;
  T.storage_not_null uint16_t_ctype uint16_t_alignof a;
  fold uint16_t_pts_to_uninit a;
}

[@@allow_ambiguous]
ghost fn uint16_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: U16.t)
  preserves uint16_t_pts_to a p1 x
  preserves uint16_t_pts_to a p2 y
  ensures   pure (x == y)
{
  unfold uint16_t_pts_to a p1 x;
  unfold uint16_t_pts_to a p2 y;
  T.agree uint16_t_ctype uint16_t_repr uint16_t_alignof uint16_t_repr_injective a;
  fold uint16_t_pts_to a p1 x;
  fold uint16_t_pts_to a p2 y;
}

ghost fn uint16_t_share (a: ptr) (#p: perm) (#x: U16.t)
  requires uint16_t_pts_to a p x
  ensures  uint16_t_pts_to a (p /. 2.0R) x ** uint16_t_pts_to a (p /. 2.0R) x
{
  unfold uint16_t_pts_to a p x;
  T.share uint16_t_ctype uint16_t_repr uint16_t_alignof a;
  fold uint16_t_pts_to a (p /. 2.0R) x;
  fold uint16_t_pts_to a (p /. 2.0R) x;
}

[@@allow_ambiguous]
ghost fn uint16_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: U16.t)
  requires uint16_t_pts_to a p1 x ** uint16_t_pts_to a p2 y
  ensures  uint16_t_pts_to a (p1 +. p2) x ** pure (x == y)
{
  unfold uint16_t_pts_to a p1 x;
  unfold uint16_t_pts_to a p2 y;
  T.gather uint16_t_ctype uint16_t_repr uint16_t_alignof uint16_t_repr_injective a;
  fold uint16_t_pts_to a (p1 +. p2) x;
}

ghost fn uint16_t_reveal (a: ptr) (#p: perm) (#x: U16.t)
  requires uint16_t_pts_to a p x
  ensures  exists* b e. mem_pts_to_at a p b e ** pure (ET.elen e == len b /\ ET.read_ok e uint16_t_ctype /\ uint16_t_repr x b /\ aligned a uint16_t_alignof)
{
  unfold uint16_t_pts_to a p x;
  T.reveal_value uint16_t_ctype uint16_t_repr uint16_t_alignof a;
}

ghost fn uint16_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: U16.t) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (uint16_t_repr x b)
  requires pure (aligned a uint16_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e uint16_t_ctype)
  ensures  uint16_t_pts_to a p x
{
  uint16_t_repr_no_prov x b;
  T.claim uint16_t_ctype uint16_t_repr uint16_t_alignof a #p #x #b #e;
  fold uint16_t_pts_to a p x;
}

ghost fn uint16_t_forget (a: ptr) (#x: U16.t)
  requires uint16_t_pts_to a 1.0R x
  ensures  uint16_t_pts_to_uninit a
{
  unfold uint16_t_pts_to a 1.0R x;
  T.forget uint16_t_ctype uint16_t_repr uint16_t_alignof a;
  fold uint16_t_pts_to_uninit a;
}

ghost fn uint16_t_claim (a: ptr) (#b: bytes) (x: U16.t) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (uint16_t_repr x b)
  requires pure (aligned a uint16_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e uint16_t_ctype)
  ensures  uint16_t_pts_to a 1.0R x
{
  uint16_t_repr_no_prov x b;
  T.claim uint16_t_ctype uint16_t_repr uint16_t_alignof a #1.0R #x #b #e;
  fold uint16_t_pts_to a 1.0R x;
}

ghost fn uint16_t_claim_uninit (a: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v uint16_t_sizeof /\ aligned a uint16_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e uint16_t_ctype)
  ensures  uint16_t_pts_to_uninit a
{
  T.claim_storage uint16_t_ctype uint16_t_alignof a;
  fold uint16_t_pts_to_uninit a;
}

ghost fn uint16_t_reveal_uninit (a: ptr)
  requires uint16_t_pts_to_uninit a
  ensures  exists* b e. mem_pts_to_at a 1.0R b e ** pure (ET.elen e == len b /\ ET.read_ok e uint16_t_ctype /\ len b == SZ.v uint16_t_sizeof /\ aligned a uint16_t_alignof)
{
  unfold uint16_t_pts_to_uninit a;
  T.reveal_storage uint16_t_ctype uint16_t_alignof a;
}

(* ------------------------------- uint64_t ------------------------------- *)



let uint64_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: U64.t) : slprop =
  T.value uint64_t_ctype uint64_t_repr uint64_t_alignof a p x

let uint64_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop =
  T.storage uint64_t_ctype uint64_t_alignof a

let uint64_t_repr_no_prov (x: U64.t) (b: bytes)
  : Lemma (requires uint64_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v uint64_t_sizeof)
  = ()

let uint64_t_repr_injective (x y: U64.t) (b: bytes)
  : Lemma (requires uint64_t_repr x b /\ uint64_t_repr y b)
          (ensures  x == y)
  = assert_norm (pow2 (8 * 8) == pow2 64);
    encode_injective (SZ.v uint64_t_sizeof) None (U64.v x) (U64.v y)

ghost fn uint64_t_pts_to_not_null (a: ptr) (#p: perm) (#x: U64.t)
  preserves uint64_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold uint64_t_pts_to a p x;
  T.not_null uint64_t_ctype uint64_t_repr uint64_t_alignof a;
  fold uint64_t_pts_to a p x;
}

ghost fn uint64_t_pts_to_uninit_not_null (a: ptr)
  preserves uint64_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold uint64_t_pts_to_uninit a;
  T.storage_not_null uint64_t_ctype uint64_t_alignof a;
  fold uint64_t_pts_to_uninit a;
}

[@@allow_ambiguous]
ghost fn uint64_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: U64.t)
  preserves uint64_t_pts_to a p1 x
  preserves uint64_t_pts_to a p2 y
  ensures   pure (x == y)
{
  unfold uint64_t_pts_to a p1 x;
  unfold uint64_t_pts_to a p2 y;
  T.agree uint64_t_ctype uint64_t_repr uint64_t_alignof uint64_t_repr_injective a;
  fold uint64_t_pts_to a p1 x;
  fold uint64_t_pts_to a p2 y;
}

ghost fn uint64_t_share (a: ptr) (#p: perm) (#x: U64.t)
  requires uint64_t_pts_to a p x
  ensures  uint64_t_pts_to a (p /. 2.0R) x ** uint64_t_pts_to a (p /. 2.0R) x
{
  unfold uint64_t_pts_to a p x;
  T.share uint64_t_ctype uint64_t_repr uint64_t_alignof a;
  fold uint64_t_pts_to a (p /. 2.0R) x;
  fold uint64_t_pts_to a (p /. 2.0R) x;
}

[@@allow_ambiguous]
ghost fn uint64_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: U64.t)
  requires uint64_t_pts_to a p1 x ** uint64_t_pts_to a p2 y
  ensures  uint64_t_pts_to a (p1 +. p2) x ** pure (x == y)
{
  unfold uint64_t_pts_to a p1 x;
  unfold uint64_t_pts_to a p2 y;
  T.gather uint64_t_ctype uint64_t_repr uint64_t_alignof uint64_t_repr_injective a;
  fold uint64_t_pts_to a (p1 +. p2) x;
}

ghost fn uint64_t_reveal (a: ptr) (#p: perm) (#x: U64.t)
  requires uint64_t_pts_to a p x
  ensures  exists* b e. mem_pts_to_at a p b e ** pure (ET.elen e == len b /\ ET.read_ok e uint64_t_ctype /\ uint64_t_repr x b /\ aligned a uint64_t_alignof)
{
  unfold uint64_t_pts_to a p x;
  T.reveal_value uint64_t_ctype uint64_t_repr uint64_t_alignof a;
}

ghost fn uint64_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: U64.t) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (uint64_t_repr x b)
  requires pure (aligned a uint64_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e uint64_t_ctype)
  ensures  uint64_t_pts_to a p x
{
  uint64_t_repr_no_prov x b;
  T.claim uint64_t_ctype uint64_t_repr uint64_t_alignof a #p #x #b #e;
  fold uint64_t_pts_to a p x;
}

ghost fn uint64_t_forget (a: ptr) (#x: U64.t)
  requires uint64_t_pts_to a 1.0R x
  ensures  uint64_t_pts_to_uninit a
{
  unfold uint64_t_pts_to a 1.0R x;
  T.forget uint64_t_ctype uint64_t_repr uint64_t_alignof a;
  fold uint64_t_pts_to_uninit a;
}

ghost fn uint64_t_claim (a: ptr) (#b: bytes) (x: U64.t) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (uint64_t_repr x b)
  requires pure (aligned a uint64_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e uint64_t_ctype)
  ensures  uint64_t_pts_to a 1.0R x
{
  uint64_t_repr_no_prov x b;
  T.claim uint64_t_ctype uint64_t_repr uint64_t_alignof a #1.0R #x #b #e;
  fold uint64_t_pts_to a 1.0R x;
}

ghost fn uint64_t_claim_uninit (a: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v uint64_t_sizeof /\ aligned a uint64_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e uint64_t_ctype)
  ensures  uint64_t_pts_to_uninit a
{
  T.claim_storage uint64_t_ctype uint64_t_alignof a;
  fold uint64_t_pts_to_uninit a;
}

ghost fn uint64_t_reveal_uninit (a: ptr)
  requires uint64_t_pts_to_uninit a
  ensures  exists* b e. mem_pts_to_at a 1.0R b e ** pure (ET.elen e == len b /\ ET.read_ok e uint64_t_ctype /\ len b == SZ.v uint64_t_sizeof /\ aligned a uint64_t_alignof)
{
  unfold uint64_t_pts_to_uninit a;
  T.reveal_storage uint64_t_ctype uint64_t_alignof a;
}

(* -------------------------------- size_t --------------------------------

   `size_t` is not a fixed-width type in C, but PAL already commits to a
   concrete target (LP64) everywhere else, so it is eight bytes here. F*'s
   `FStar.SizeT.fits` is abstract, so the bound that `encode` needs is not
   derivable and has to be assumed -- exactly as for `Ptr.addr_bound`, and
   recorded alongside it under "Known deviations". *)

let size_t_bound (x: SZ.t) : Lemma (SZ.v x < pow2 64) [SMTPat (SZ.v x)] =
  assume (SZ.v x < pow2 64)

(* LP64 again: `size_t` is sixty-four bits wide, so `FStar.SizeT.fits_u64`
   holds. F* keeps it abstract, so the conversions out of the fixed-width
   unsigned types are unavailable without assuming it -- the same assumption as
   `size_t_bound`, stated where the casts need it. *)

let sizet_of_uint16 (x: U16.t) : Pure SZ.t (requires True) (ensures fun y -> SZ.v y == U16.v x) =
  SZ.uint16_to_sizet x

let sizet_of_uint32 (x: U32.t) : Pure SZ.t (requires True) (ensures fun y -> SZ.v y == U32.v x) =
  assume SZ.fits_u64;
  SZ.fits_u64_implies_fits_32 ();
  SZ.uint32_to_sizet x

let sizet_of_uint64 (x: U64.t) : Pure SZ.t (requires True) (ensures fun y -> SZ.v y == U64.v x) =
  assume SZ.fits_u64;
  SZ.uint64_to_sizet x

let size_t_fits (x: int) : Lemma (requires 0 <= x /\ x < pow2 64) (ensures SZ.fits x)
  [SMTPat (SZ.fits x)] =
  assume SZ.fits_u64;
  SZ.fits_u64_implies_fits x




let size_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: SZ.t) : slprop =
  T.value size_t_ctype size_t_repr size_t_alignof a p x

let size_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop =
  T.storage size_t_ctype size_t_alignof a

let size_t_repr_no_prov (x: SZ.t) (b: bytes)
  : Lemma (requires size_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v size_t_sizeof)
  = ()

let size_t_repr_injective (x y: SZ.t) (b: bytes)
  : Lemma (requires size_t_repr x b /\ size_t_repr y b)
          (ensures  x == y)
  = assert_norm (pow2 (8 * 8) == pow2 64);
    encode_injective (SZ.v size_t_sizeof) None (SZ.v x) (SZ.v y)

ghost fn size_t_pts_to_not_null (a: ptr) (#p: perm) (#x: SZ.t)
  preserves size_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold size_t_pts_to a p x;
  T.not_null size_t_ctype size_t_repr size_t_alignof a;
  fold size_t_pts_to a p x;
}

ghost fn size_t_pts_to_uninit_not_null (a: ptr)
  preserves size_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold size_t_pts_to_uninit a;
  T.storage_not_null size_t_ctype size_t_alignof a;
  fold size_t_pts_to_uninit a;
}

[@@allow_ambiguous]
ghost fn size_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: SZ.t)
  preserves size_t_pts_to a p1 x
  preserves size_t_pts_to a p2 y
  ensures   pure (x == y)
{
  unfold size_t_pts_to a p1 x;
  unfold size_t_pts_to a p2 y;
  T.agree size_t_ctype size_t_repr size_t_alignof size_t_repr_injective a;
  fold size_t_pts_to a p1 x;
  fold size_t_pts_to a p2 y;
}

ghost fn size_t_share (a: ptr) (#p: perm) (#x: SZ.t)
  requires size_t_pts_to a p x
  ensures  size_t_pts_to a (p /. 2.0R) x ** size_t_pts_to a (p /. 2.0R) x
{
  unfold size_t_pts_to a p x;
  T.share size_t_ctype size_t_repr size_t_alignof a;
  fold size_t_pts_to a (p /. 2.0R) x;
  fold size_t_pts_to a (p /. 2.0R) x;
}

[@@allow_ambiguous]
ghost fn size_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: SZ.t)
  requires size_t_pts_to a p1 x ** size_t_pts_to a p2 y
  ensures  size_t_pts_to a (p1 +. p2) x ** pure (x == y)
{
  unfold size_t_pts_to a p1 x;
  unfold size_t_pts_to a p2 y;
  T.gather size_t_ctype size_t_repr size_t_alignof size_t_repr_injective a;
  fold size_t_pts_to a (p1 +. p2) x;
}

ghost fn size_t_reveal (a: ptr) (#p: perm) (#x: SZ.t)
  requires size_t_pts_to a p x
  ensures  exists* b e. mem_pts_to_at a p b e ** pure (ET.elen e == len b /\ ET.read_ok e size_t_ctype /\ size_t_repr x b /\ aligned a size_t_alignof)
{
  unfold size_t_pts_to a p x;
  T.reveal_value size_t_ctype size_t_repr size_t_alignof a;
}

ghost fn size_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: SZ.t) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (size_t_repr x b)
  requires pure (aligned a size_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e size_t_ctype)
  ensures  size_t_pts_to a p x
{
  size_t_repr_no_prov x b;
  T.claim size_t_ctype size_t_repr size_t_alignof a #p #x #b #e;
  fold size_t_pts_to a p x;
}

ghost fn size_t_forget (a: ptr) (#x: SZ.t)
  requires size_t_pts_to a 1.0R x
  ensures  size_t_pts_to_uninit a
{
  unfold size_t_pts_to a 1.0R x;
  T.forget size_t_ctype size_t_repr size_t_alignof a;
  fold size_t_pts_to_uninit a;
}

ghost fn size_t_claim (a: ptr) (#b: bytes) (x: SZ.t) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (size_t_repr x b)
  requires pure (aligned a size_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e size_t_ctype)
  ensures  size_t_pts_to a 1.0R x
{
  size_t_repr_no_prov x b;
  T.claim size_t_ctype size_t_repr size_t_alignof a #1.0R #x #b #e;
  fold size_t_pts_to a 1.0R x;
}

ghost fn size_t_claim_uninit (a: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v size_t_sizeof /\ aligned a size_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e size_t_ctype)
  ensures  size_t_pts_to_uninit a
{
  T.claim_storage size_t_ctype size_t_alignof a;
  fold size_t_pts_to_uninit a;
}

ghost fn size_t_reveal_uninit (a: ptr)
  requires size_t_pts_to_uninit a
  ensures  exists* b e. mem_pts_to_at a 1.0R b e ** pure (ET.elen e == len b /\ ET.read_ok e size_t_ctype /\ len b == SZ.v size_t_sizeof /\ aligned a size_t_alignof)
{
  unfold size_t_pts_to_uninit a;
  T.reveal_storage size_t_ctype size_t_alignof a;
}


(* ------------------------------- uint8_t -------------------------------

   `uint8_t`'s size, representation and points-to are in
   `Pulse.Lib.C.Palow.Scalar`, where the aggregate proofs need them; only the
   derived set is missing, and it is the same set as every other type's. *)

let uint8_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop =
  T.storage uint8_t_ctype uint8_t_alignof a

let uint8_t_repr_no_prov (x: U8.t) (b: bytes)
  : Lemma (requires uint8_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v uint8_t_sizeof)
  = ()

let uint8_t_repr_injective (x y: U8.t) (b: bytes)
  : Lemma (requires uint8_t_repr x b /\ uint8_t_repr y b)
          (ensures  x == y)
  = assert_norm (pow2 (8 * 1) == pow2 8);
    encode_injective (SZ.v uint8_t_sizeof) None (U8.v x) (U8.v y)

ghost fn uint8_t_pts_to_not_null (a: ptr) (#p: perm) (#x: U8.t)
  preserves uint8_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  uint8_t_reveal a;
  with b e. assert (mem_pts_to_at a p b e);
  mem_pts_to_at_not_null a;
  uint8_t_conceal a #p #b #x #e;
}

ghost fn uint8_t_pts_to_uninit_not_null (a: ptr)
  preserves uint8_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold uint8_t_pts_to_uninit a;
  T.storage_not_null uint8_t_ctype uint8_t_alignof a;
  fold uint8_t_pts_to_uninit a;
}

[@@allow_ambiguous]
ghost fn uint8_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: U8.t)
  preserves uint8_t_pts_to a p1 x
  preserves uint8_t_pts_to a p2 y
  ensures   pure (x == y)
{
  uint8_t_reveal a #p1 #x;
  with b1 e1. assert (mem_pts_to_at a p1 b1 e1);
  uint8_t_reveal a #p2 #y;
  with b2 e2. assert (mem_pts_to_at a p2 b2 e2);
  mem_pts_to_at_bytes_injective a;
  uint8_t_repr_injective x y b1;
  uint8_t_conceal a #p1 #b1 #x #e1;
  uint8_t_conceal a #p2 #b2 #y #e2;
}

ghost fn uint8_t_share (a: ptr) (#p: perm) (#x: U8.t)
  requires uint8_t_pts_to a p x
  ensures  uint8_t_pts_to a (p /. 2.0R) x ** uint8_t_pts_to a (p /. 2.0R) x
{
  uint8_t_reveal a;
  with b e. assert (mem_pts_to_at a p b e);
  mem_share_at a;
  uint8_t_conceal a #(p /. 2.0R) #b #x #e;
  uint8_t_conceal a #(p /. 2.0R) #b #x #e;
}

[@@allow_ambiguous]
ghost fn uint8_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: U8.t)
  requires uint8_t_pts_to a p1 x ** uint8_t_pts_to a p2 y
  ensures  uint8_t_pts_to a (p1 +. p2) x ** pure (x == y)
{
  uint8_t_reveal a #p1 #x;
  with b1 e1. assert (mem_pts_to_at a p1 b1 e1);
  uint8_t_reveal a #p2 #y;
  with b2 e2. assert (mem_pts_to_at a p2 b2 e2);
  mem_gather_at a;
  uint8_t_repr_injective x y b1;
  uint8_t_conceal a #(p1 +. p2) #b1 #x #e1;
}

ghost fn uint8_t_forget (a: ptr) (#x: U8.t)
  requires uint8_t_pts_to a 1.0R x
  ensures  uint8_t_pts_to_uninit a
{
  uint8_t_reveal a;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  T.claim_storage uint8_t_ctype uint8_t_alignof a;
  fold uint8_t_pts_to_uninit a;
}

ghost fn uint8_t_claim (a: ptr) (#b: bytes) (x: U8.t) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (uint8_t_repr x b)
  requires pure (aligned a uint8_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e uint8_t_ctype)
  ensures  uint8_t_pts_to a 1.0R x
{
  uint8_t_conceal a #1.0R #b #x #e;
}

ghost fn uint8_t_claim_uninit (a: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v uint8_t_sizeof /\ aligned a uint8_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e uint8_t_ctype)
  ensures  uint8_t_pts_to_uninit a
{
  T.claim_storage uint8_t_ctype uint8_t_alignof a;
  fold uint8_t_pts_to_uninit a;
}

ghost fn uint8_t_reveal_uninit (a: ptr)
  requires uint8_t_pts_to_uninit a
  ensures  exists* b e. mem_pts_to_at a 1.0R b e ** pure (ET.elen e == len b /\ ET.read_ok e uint8_t_ctype /\ len b == SZ.v uint8_t_sizeof /\ aligned a uint8_t_alignof)
{
  unfold uint8_t_pts_to_uninit a;
  T.reveal_storage uint8_t_ctype uint8_t_alignof a;
}

(* ---------------------------------------------------------------------------
   Elements of an array

   `array_focus` hands back an `elem_pts_to t_ctype t_repr`, which is the generic
   "there exist bytes representing this value" form. Every scalar type has its
   own points-to predicate instead, so each one gets a pair of ghost functions
   trading between the two. They are what makes an emitted subscript short: the
   value stays implicit throughout, so PAL never has to name `Seq.index xs i`.
   --------------------------------------------------------------------------- *)

ghost fn bool_t_of_elem (a: ptr) (#p: perm) (#x: bool)
  requires elem_pts_to bool_t_ctype bool_t_repr a p x
  requires pure (aligned a bool_t_alignof)
  ensures  bool_t_pts_to a p x
{
  elem_reveal bool_t_ctype bool_t_repr a;
  bool_t_conceal a #p #_ #x;
}

ghost fn bool_t_to_elem (a: ptr) (#p: perm) (#x: bool)
  requires bool_t_pts_to a p x
  ensures  elem_pts_to bool_t_ctype bool_t_repr a p x
  ensures  pure (aligned a bool_t_alignof)
{
  bool_t_reveal a;
  elem_conceal bool_t_ctype bool_t_repr a #p #_ #x;
}

ghost fn int8_t_of_elem (a: ptr) (#p: perm) (#x: I8.t)
  requires elem_pts_to int8_t_ctype int8_t_repr a p x
  requires pure (aligned a int8_t_alignof)
  ensures  int8_t_pts_to a p x
{
  elem_reveal int8_t_ctype int8_t_repr a;
  int8_t_conceal a #p #_ #x;
}

ghost fn int8_t_to_elem (a: ptr) (#p: perm) (#x: I8.t)
  requires int8_t_pts_to a p x
  ensures  elem_pts_to int8_t_ctype int8_t_repr a p x
  ensures  pure (aligned a int8_t_alignof)
{
  int8_t_reveal a;
  elem_conceal int8_t_ctype int8_t_repr a #p #_ #x;
}

ghost fn int16_t_of_elem (a: ptr) (#p: perm) (#x: I16.t)
  requires elem_pts_to int16_t_ctype int16_t_repr a p x
  requires pure (aligned a int16_t_alignof)
  ensures  int16_t_pts_to a p x
{
  elem_reveal int16_t_ctype int16_t_repr a;
  int16_t_conceal a #p #_ #x;
}

ghost fn int16_t_to_elem (a: ptr) (#p: perm) (#x: I16.t)
  requires int16_t_pts_to a p x
  ensures  elem_pts_to int16_t_ctype int16_t_repr a p x
  ensures  pure (aligned a int16_t_alignof)
{
  int16_t_reveal a;
  elem_conceal int16_t_ctype int16_t_repr a #p #_ #x;
}

ghost fn int32_t_of_elem (a: ptr) (#p: perm) (#x: I32.t)
  requires elem_pts_to int32_t_ctype int32_t_repr a p x
  requires pure (aligned a int32_t_alignof)
  ensures  int32_t_pts_to a p x
{
  elem_reveal int32_t_ctype int32_t_repr a;
  int32_t_conceal a #p #_ #x;
}

ghost fn int32_t_to_elem (a: ptr) (#p: perm) (#x: I32.t)
  requires int32_t_pts_to a p x
  ensures  elem_pts_to int32_t_ctype int32_t_repr a p x
  ensures  pure (aligned a int32_t_alignof)
{
  int32_t_reveal a;
  elem_conceal int32_t_ctype int32_t_repr a #p #_ #x;
}

ghost fn int64_t_of_elem (a: ptr) (#p: perm) (#x: I64.t)
  requires elem_pts_to int64_t_ctype int64_t_repr a p x
  requires pure (aligned a int64_t_alignof)
  ensures  int64_t_pts_to a p x
{
  elem_reveal int64_t_ctype int64_t_repr a;
  int64_t_conceal a #p #_ #x;
}

ghost fn int64_t_to_elem (a: ptr) (#p: perm) (#x: I64.t)
  requires int64_t_pts_to a p x
  ensures  elem_pts_to int64_t_ctype int64_t_repr a p x
  ensures  pure (aligned a int64_t_alignof)
{
  int64_t_reveal a;
  elem_conceal int64_t_ctype int64_t_repr a #p #_ #x;
}

ghost fn uint16_t_of_elem (a: ptr) (#p: perm) (#x: U16.t)
  requires elem_pts_to uint16_t_ctype uint16_t_repr a p x
  requires pure (aligned a uint16_t_alignof)
  ensures  uint16_t_pts_to a p x
{
  elem_reveal uint16_t_ctype uint16_t_repr a;
  uint16_t_conceal a #p #_ #x;
}

ghost fn uint16_t_to_elem (a: ptr) (#p: perm) (#x: U16.t)
  requires uint16_t_pts_to a p x
  ensures  elem_pts_to uint16_t_ctype uint16_t_repr a p x
  ensures  pure (aligned a uint16_t_alignof)
{
  uint16_t_reveal a;
  elem_conceal uint16_t_ctype uint16_t_repr a #p #_ #x;
}

ghost fn uint64_t_of_elem (a: ptr) (#p: perm) (#x: U64.t)
  requires elem_pts_to uint64_t_ctype uint64_t_repr a p x
  requires pure (aligned a uint64_t_alignof)
  ensures  uint64_t_pts_to a p x
{
  elem_reveal uint64_t_ctype uint64_t_repr a;
  uint64_t_conceal a #p #_ #x;
}

ghost fn uint64_t_to_elem (a: ptr) (#p: perm) (#x: U64.t)
  requires uint64_t_pts_to a p x
  ensures  elem_pts_to uint64_t_ctype uint64_t_repr a p x
  ensures  pure (aligned a uint64_t_alignof)
{
  uint64_t_reveal a;
  elem_conceal uint64_t_ctype uint64_t_repr a #p #_ #x;
}

ghost fn size_t_of_elem (a: ptr) (#p: perm) (#x: SZ.t)
  requires elem_pts_to size_t_ctype size_t_repr a p x
  requires pure (aligned a size_t_alignof)
  ensures  size_t_pts_to a p x
{
  elem_reveal size_t_ctype size_t_repr a;
  size_t_conceal a #p #_ #x;
}

ghost fn size_t_to_elem (a: ptr) (#p: perm) (#x: SZ.t)
  requires size_t_pts_to a p x
  ensures  elem_pts_to size_t_ctype size_t_repr a p x
  ensures  pure (aligned a size_t_alignof)
{
  size_t_reveal a;
  elem_conceal size_t_ctype size_t_repr a #p #_ #x;
}

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



let float32_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: float32) : slprop =
  T.value float32_t_ctype float32_t_repr float32_t_alignof a p x

let float32_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop =
  T.storage float32_t_ctype float32_t_alignof a

let float32_t_repr_no_prov (x: float32) (b: bytes)
  : Lemma (requires float32_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v float32_t_sizeof)
  = ()

let float32_t_repr_injective (x y: float32) (b: bytes)
  : Lemma (requires float32_t_repr x b /\ float32_t_repr y b)
          (ensures  x == y)
  = assert_norm (pow2 (8 * 4) == pow2 32);
    encode_injective (SZ.v float32_t_sizeof) None (float32_bits x) (float32_bits y);
    float32_bits_injective x y

ghost fn float32_t_pts_to_not_null (a: ptr) (#p: perm) (#x: float32)
  preserves float32_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold float32_t_pts_to a p x;
  T.not_null float32_t_ctype float32_t_repr float32_t_alignof a;
  fold float32_t_pts_to a p x;
}

ghost fn float32_t_pts_to_uninit_not_null (a: ptr)
  preserves float32_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold float32_t_pts_to_uninit a;
  T.storage_not_null float32_t_ctype float32_t_alignof a;
  fold float32_t_pts_to_uninit a;
}

[@@allow_ambiguous]
ghost fn float32_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: float32)
  preserves float32_t_pts_to a p1 x
  preserves float32_t_pts_to a p2 y
  ensures   pure (x == y)
{
  unfold float32_t_pts_to a p1 x;
  unfold float32_t_pts_to a p2 y;
  T.agree float32_t_ctype float32_t_repr float32_t_alignof float32_t_repr_injective a;
  fold float32_t_pts_to a p1 x;
  fold float32_t_pts_to a p2 y;
}

ghost fn float32_t_share (a: ptr) (#p: perm) (#x: float32)
  requires float32_t_pts_to a p x
  ensures  float32_t_pts_to a (p /. 2.0R) x ** float32_t_pts_to a (p /. 2.0R) x
{
  unfold float32_t_pts_to a p x;
  T.share float32_t_ctype float32_t_repr float32_t_alignof a;
  fold float32_t_pts_to a (p /. 2.0R) x;
  fold float32_t_pts_to a (p /. 2.0R) x;
}

[@@allow_ambiguous]
ghost fn float32_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: float32)
  requires float32_t_pts_to a p1 x ** float32_t_pts_to a p2 y
  ensures  float32_t_pts_to a (p1 +. p2) x ** pure (x == y)
{
  unfold float32_t_pts_to a p1 x;
  unfold float32_t_pts_to a p2 y;
  T.gather float32_t_ctype float32_t_repr float32_t_alignof float32_t_repr_injective a;
  fold float32_t_pts_to a (p1 +. p2) x;
}

ghost fn float32_t_reveal (a: ptr) (#p: perm) (#x: float32)
  requires float32_t_pts_to a p x
  ensures  exists* b e. mem_pts_to_at a p b e ** pure (ET.elen e == len b /\ ET.read_ok e float32_t_ctype /\ float32_t_repr x b /\ aligned a float32_t_alignof)
{
  unfold float32_t_pts_to a p x;
  T.reveal_value float32_t_ctype float32_t_repr float32_t_alignof a;
}

ghost fn float32_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: float32) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (float32_t_repr x b)
  requires pure (aligned a float32_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e float32_t_ctype)
  ensures  float32_t_pts_to a p x
{
  float32_t_repr_no_prov x b;
  T.claim float32_t_ctype float32_t_repr float32_t_alignof a #p #x #b #e;
  fold float32_t_pts_to a p x;
}

ghost fn float32_t_forget (a: ptr) (#x: float32)
  requires float32_t_pts_to a 1.0R x
  ensures  float32_t_pts_to_uninit a
{
  unfold float32_t_pts_to a 1.0R x;
  T.forget float32_t_ctype float32_t_repr float32_t_alignof a;
  fold float32_t_pts_to_uninit a;
}

ghost fn float32_t_claim (a: ptr) (#b: bytes) (x: float32) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (float32_t_repr x b)
  requires pure (aligned a float32_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e float32_t_ctype)
  ensures  float32_t_pts_to a 1.0R x
{
  float32_t_repr_no_prov x b;
  T.claim float32_t_ctype float32_t_repr float32_t_alignof a #1.0R #x #b #e;
  fold float32_t_pts_to a 1.0R x;
}

ghost fn float32_t_claim_uninit (a: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v float32_t_sizeof /\ aligned a float32_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e float32_t_ctype)
  ensures  float32_t_pts_to_uninit a
{
  T.claim_storage float32_t_ctype float32_t_alignof a;
  fold float32_t_pts_to_uninit a;
}

ghost fn float32_t_reveal_uninit (a: ptr)
  requires float32_t_pts_to_uninit a
  ensures  exists* b e. mem_pts_to_at a 1.0R b e ** pure (ET.elen e == len b /\ ET.read_ok e float32_t_ctype /\ len b == SZ.v float32_t_sizeof /\ aligned a float32_t_alignof)
{
  unfold float32_t_pts_to_uninit a;
  T.reveal_storage float32_t_ctype float32_t_alignof a;
}

(* ------------------------------ float64_t ------------------------------ *)



let float64_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: float64) : slprop =
  T.value float64_t_ctype float64_t_repr float64_t_alignof a p x

let float64_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop =
  T.storage float64_t_ctype float64_t_alignof a

let float64_t_repr_no_prov (x: float64) (b: bytes)
  : Lemma (requires float64_t_repr x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v float64_t_sizeof)
  = ()

let float64_t_repr_injective (x y: float64) (b: bytes)
  : Lemma (requires float64_t_repr x b /\ float64_t_repr y b)
          (ensures  x == y)
  = assert_norm (pow2 (8 * 8) == pow2 64);
    encode_injective (SZ.v float64_t_sizeof) None (float64_bits x) (float64_bits y);
    float64_bits_injective x y

ghost fn float64_t_pts_to_not_null (a: ptr) (#p: perm) (#x: float64)
  preserves float64_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold float64_t_pts_to a p x;
  T.not_null float64_t_ctype float64_t_repr float64_t_alignof a;
  fold float64_t_pts_to a p x;
}

ghost fn float64_t_pts_to_uninit_not_null (a: ptr)
  preserves float64_t_pts_to_uninit a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold float64_t_pts_to_uninit a;
  T.storage_not_null float64_t_ctype float64_t_alignof a;
  fold float64_t_pts_to_uninit a;
}

[@@allow_ambiguous]
ghost fn float64_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: float64)
  preserves float64_t_pts_to a p1 x
  preserves float64_t_pts_to a p2 y
  ensures   pure (x == y)
{
  unfold float64_t_pts_to a p1 x;
  unfold float64_t_pts_to a p2 y;
  T.agree float64_t_ctype float64_t_repr float64_t_alignof float64_t_repr_injective a;
  fold float64_t_pts_to a p1 x;
  fold float64_t_pts_to a p2 y;
}

ghost fn float64_t_share (a: ptr) (#p: perm) (#x: float64)
  requires float64_t_pts_to a p x
  ensures  float64_t_pts_to a (p /. 2.0R) x ** float64_t_pts_to a (p /. 2.0R) x
{
  unfold float64_t_pts_to a p x;
  T.share float64_t_ctype float64_t_repr float64_t_alignof a;
  fold float64_t_pts_to a (p /. 2.0R) x;
  fold float64_t_pts_to a (p /. 2.0R) x;
}

[@@allow_ambiguous]
ghost fn float64_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: float64)
  requires float64_t_pts_to a p1 x ** float64_t_pts_to a p2 y
  ensures  float64_t_pts_to a (p1 +. p2) x ** pure (x == y)
{
  unfold float64_t_pts_to a p1 x;
  unfold float64_t_pts_to a p2 y;
  T.gather float64_t_ctype float64_t_repr float64_t_alignof float64_t_repr_injective a;
  fold float64_t_pts_to a (p1 +. p2) x;
}

ghost fn float64_t_reveal (a: ptr) (#p: perm) (#x: float64)
  requires float64_t_pts_to a p x
  ensures  exists* b e. mem_pts_to_at a p b e ** pure (ET.elen e == len b /\ ET.read_ok e float64_t_ctype /\ float64_t_repr x b /\ aligned a float64_t_alignof)
{
  unfold float64_t_pts_to a p x;
  T.reveal_value float64_t_ctype float64_t_repr float64_t_alignof a;
}

ghost fn float64_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: float64) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (float64_t_repr x b)
  requires pure (aligned a float64_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e float64_t_ctype)
  ensures  float64_t_pts_to a p x
{
  float64_t_repr_no_prov x b;
  T.claim float64_t_ctype float64_t_repr float64_t_alignof a #p #x #b #e;
  fold float64_t_pts_to a p x;
}

ghost fn float64_t_forget (a: ptr) (#x: float64)
  requires float64_t_pts_to a 1.0R x
  ensures  float64_t_pts_to_uninit a
{
  unfold float64_t_pts_to a 1.0R x;
  T.forget float64_t_ctype float64_t_repr float64_t_alignof a;
  fold float64_t_pts_to_uninit a;
}

ghost fn float64_t_claim (a: ptr) (#b: bytes) (x: float64) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (float64_t_repr x b)
  requires pure (aligned a float64_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e float64_t_ctype)
  ensures  float64_t_pts_to a 1.0R x
{
  float64_t_repr_no_prov x b;
  T.claim float64_t_ctype float64_t_repr float64_t_alignof a #1.0R #x #b #e;
  fold float64_t_pts_to a 1.0R x;
}

ghost fn float64_t_claim_uninit (a: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v float64_t_sizeof /\ aligned a float64_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e float64_t_ctype)
  ensures  float64_t_pts_to_uninit a
{
  T.claim_storage float64_t_ctype float64_t_alignof a;
  fold float64_t_pts_to_uninit a;
}

ghost fn float64_t_reveal_uninit (a: ptr)
  requires float64_t_pts_to_uninit a
  ensures  exists* b e. mem_pts_to_at a 1.0R b e ** pure (ET.elen e == len b /\ ET.read_ok e float64_t_ctype /\ len b == SZ.v float64_t_sizeof /\ aligned a float64_t_alignof)
{
  unfold float64_t_pts_to_uninit a;
  T.reveal_storage float64_t_ctype float64_t_alignof a;
}


ghost fn float32_t_of_elem (a: ptr) (#p: perm) (#x: float32)
  requires elem_pts_to float32_t_ctype float32_t_repr a p x
  requires pure (aligned a float32_t_alignof)
  ensures  float32_t_pts_to a p x
{
  elem_reveal float32_t_ctype float32_t_repr a;
  float32_t_conceal a #p #_ #x;
}

ghost fn float32_t_to_elem (a: ptr) (#p: perm) (#x: float32)
  requires float32_t_pts_to a p x
  ensures  elem_pts_to float32_t_ctype float32_t_repr a p x
  ensures  pure (aligned a float32_t_alignof)
{
  float32_t_reveal a;
  elem_conceal float32_t_ctype float32_t_repr a #p #_ #x;
}


ghost fn float64_t_of_elem (a: ptr) (#p: perm) (#x: float64)
  requires elem_pts_to float64_t_ctype float64_t_repr a p x
  requires pure (aligned a float64_t_alignof)
  ensures  float64_t_pts_to a p x
{
  elem_reveal float64_t_ctype float64_t_repr a;
  float64_t_conceal a #p #_ #x;
}

ghost fn float64_t_to_elem (a: ptr) (#p: perm) (#x: float64)
  requires float64_t_pts_to a p x
  ensures  elem_pts_to float64_t_ctype float64_t_repr a p x
  ensures  pure (aligned a float64_t_alignof)
{
  float64_t_reveal a;
  elem_conceal float64_t_ctype float64_t_repr a #p #_ #x;
}
