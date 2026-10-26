module Pulse.Lib.C.Palow.Enum.Base

(* Enumerated types (6.7.2.2). An enumerated type has the size, alignment and
   representation of its underlying integer type, here `unsigned int` or
   `int`, but it is a distinct type: its effective-type descriptor is
   `ET.SEnum tag base`, so two different enumerated types do not alias each
   other while either one may still be accessed through its underlying type or
   that type's signed/unsigned counterpart (6.5p7).

   One family per underlying type, parameterized by the enumeration's tag.
   PAL emits, per enumeration, an `Enum_<tag>` module of `unfold` aliases
   (`enum_u32_color_read = enum_u32_read "color"`, ...).

   Generated from the 16-bit blocks of Pulse.Lib.C.Palow.CTypes. *)

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
open Pulse.Lib.C.Palow.CTypes


let enum_u32_pts_to (tag: string) ([@@@mkey] a: ptr) (p: perm) (x: U32.t) : slprop =
  T.value (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a p x

let enum_u32_pts_to_uninit (tag: string) ([@@@mkey] a: ptr) : slprop =
  T.storage (enum_u32_ctype tag) (enum_u32_alignof tag) a

let enum_u32_repr_no_prov (tag: string) (x: U32.t) (b: bytes)
  : Lemma (requires (enum_u32_repr tag) x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v (enum_u32_sizeof tag))
  = ()

let enum_u32_repr_injective (tag: string) (x y: U32.t) (b: bytes)
  : Lemma (requires (enum_u32_repr tag) x b /\ (enum_u32_repr tag) y b)
          (ensures  x == y)
  = assert_norm (pow2 (8 * 4) == pow2 32);
    encode_injective (SZ.v (enum_u32_sizeof tag)) None (U32.v x) (U32.v y)

ghost fn enum_u32_pts_to_not_null (tag: string) (a: ptr) (#p: perm) (#x: U32.t)
  preserves (enum_u32_pts_to tag) a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold (enum_u32_pts_to tag) a p x;
  T.not_null (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a;
  fold (enum_u32_pts_to tag) a p x;
}

ghost fn enum_u32_pts_to_uninit_not_null (tag: string) (a: ptr)
  preserves (enum_u32_pts_to_uninit tag) a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold (enum_u32_pts_to_uninit tag) a;
  T.storage_not_null (enum_u32_ctype tag) (enum_u32_alignof tag) a;
  fold (enum_u32_pts_to_uninit tag) a;
}

[@@allow_ambiguous]
ghost fn enum_u32_agree (tag: string) (a: ptr) (#p1 #p2: perm) (#x #y: U32.t)
  preserves (enum_u32_pts_to tag) a p1 x
  preserves (enum_u32_pts_to tag) a p2 y
  ensures   pure (x == y)
{
  unfold (enum_u32_pts_to tag) a p1 x;
  unfold (enum_u32_pts_to tag) a p2 y;
  T.agree (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) (enum_u32_repr_injective tag) a;
  fold (enum_u32_pts_to tag) a p1 x;
  fold (enum_u32_pts_to tag) a p2 y;
}

ghost fn enum_u32_share (tag: string) (a: ptr) (#p: perm) (#x: U32.t)
  requires (enum_u32_pts_to tag) a p x
  ensures  (enum_u32_pts_to tag) a (p /. 2.0R) x ** (enum_u32_pts_to tag) a (p /. 2.0R) x
{
  unfold (enum_u32_pts_to tag) a p x;
  T.share (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a;
  fold (enum_u32_pts_to tag) a (p /. 2.0R) x;
  fold (enum_u32_pts_to tag) a (p /. 2.0R) x;
}

[@@allow_ambiguous]
ghost fn enum_u32_gather (tag: string) (a: ptr) (#p1 #p2: perm) (#x #y: U32.t)
  requires (enum_u32_pts_to tag) a p1 x ** (enum_u32_pts_to tag) a p2 y
  ensures  (enum_u32_pts_to tag) a (p1 +. p2) x ** pure (x == y)
{
  unfold (enum_u32_pts_to tag) a p1 x;
  unfold (enum_u32_pts_to tag) a p2 y;
  T.gather (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) (enum_u32_repr_injective tag) a;
  fold (enum_u32_pts_to tag) a (p1 +. p2) x;
}

ghost fn enum_u32_reveal (tag: string) (a: ptr) (#p: perm) (#x: U32.t)
  requires (enum_u32_pts_to tag) a p x
  ensures  exists* b e. mem_pts_to_at a p b e ** pure (ET.elen e == len b /\ ET.read_ok e (enum_u32_ctype tag) /\ (enum_u32_repr tag) x b /\ aligned a (enum_u32_alignof tag))
{
  unfold (enum_u32_pts_to tag) a p x;
  T.reveal_value (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a;
}

ghost fn enum_u32_conceal (tag: string) (a: ptr) (#p: perm) (#b: bytes) (#x: U32.t) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure ((enum_u32_repr tag) x b)
  requires pure (aligned a (enum_u32_alignof tag))
  requires pure (ET.elen e == len b /\ ET.read_ok e (enum_u32_ctype tag))
  ensures  (enum_u32_pts_to tag) a p x
{
  (enum_u32_repr_no_prov tag) x b;
  T.claim (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a #p #x #b #e;
  fold (enum_u32_pts_to tag) a p x;
}

ghost fn enum_u32_forget (tag: string) (a: ptr) (#x: U32.t)
  requires (enum_u32_pts_to tag) a 1.0R x
  ensures  (enum_u32_pts_to_uninit tag) a
{
  unfold (enum_u32_pts_to tag) a 1.0R x;
  T.forget (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a;
  fold (enum_u32_pts_to_uninit tag) a;
}

ghost fn enum_u32_claim (tag: string) (a: ptr) (#b: bytes) (x: U32.t) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure ((enum_u32_repr tag) x b)
  requires pure (aligned a (enum_u32_alignof tag))
  requires pure (ET.elen e == len b /\ ET.read_ok e (enum_u32_ctype tag))
  ensures  (enum_u32_pts_to tag) a 1.0R x
{
  (enum_u32_repr_no_prov tag) x b;
  T.claim (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a #1.0R #x #b #e;
  fold (enum_u32_pts_to tag) a 1.0R x;
}

ghost fn enum_u32_claim_uninit (tag: string) (a: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v (enum_u32_sizeof tag) /\ aligned a (enum_u32_alignof tag))
  requires pure (ET.elen e == len b /\ ET.read_ok e (enum_u32_ctype tag))
  ensures  (enum_u32_pts_to_uninit tag) a
{
  T.claim_storage (enum_u32_ctype tag) (enum_u32_alignof tag) a;
  fold (enum_u32_pts_to_uninit tag) a;
}

ghost fn enum_u32_reveal_uninit (tag: string) (a: ptr)
  requires (enum_u32_pts_to_uninit tag) a
  ensures  exists* b e. mem_pts_to_at a 1.0R b e ** pure (ET.elen e == len b /\ ET.read_ok e (enum_u32_ctype tag) /\ len b == SZ.v (enum_u32_sizeof tag) /\ aligned a (enum_u32_alignof tag))
{
  unfold (enum_u32_pts_to_uninit tag) a;
  T.reveal_storage (enum_u32_ctype tag) (enum_u32_alignof tag) a;
}

ghost fn enum_u32_of_elem (tag: string) (a: ptr) (#p: perm) (#x: U32.t)
  requires elem_pts_to (enum_u32_ctype tag) (enum_u32_repr tag) a p x
  requires pure (aligned a (enum_u32_alignof tag))
  ensures  (enum_u32_pts_to tag) a p x
{
  elem_reveal (enum_u32_ctype tag) (enum_u32_repr tag) a;
  (enum_u32_conceal tag) a #p #_ #x;
}

ghost fn enum_u32_to_elem (tag: string) (a: ptr) (#p: perm) (#x: U32.t)
  requires (enum_u32_pts_to tag) a p x
  ensures  elem_pts_to (enum_u32_ctype tag) (enum_u32_repr tag) a p x
  ensures  pure (aligned a (enum_u32_alignof tag))
{
  (enum_u32_reveal tag) a;
  elem_conceal (enum_u32_ctype tag) (enum_u32_repr tag) a #p #_ #x;
}

let enum_i32_pts_to (tag: string) ([@@@mkey] a: ptr) (p: perm) (x: I32.t) : slprop =
  T.value (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a p x

let enum_i32_pts_to_uninit (tag: string) ([@@@mkey] a: ptr) : slprop =
  T.storage (enum_i32_ctype tag) (enum_i32_alignof tag) a

let enum_i32_repr_no_prov (tag: string) (x: I32.t) (b: bytes)
  : Lemma (requires (enum_i32_repr tag) x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v (enum_i32_sizeof tag))
  = ()

let enum_i32_repr_injective (tag: string) (x y: I32.t) (b: bytes)
  : Lemma (requires (enum_i32_repr tag) x b /\ (enum_i32_repr tag) y b)
          (ensures  x == y)
  = assert_norm (pow2 (8 * 4) == pow2 32);
    encode_injective (SZ.v (enum_i32_sizeof tag)) None (to_bits 32 (I32.v x)) (to_bits 32 (I32.v y));
    to_bits_injective 32 (I32.v x) (I32.v y)

ghost fn enum_i32_pts_to_not_null (tag: string) (a: ptr) (#p: perm) (#x: I32.t)
  preserves (enum_i32_pts_to tag) a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold (enum_i32_pts_to tag) a p x;
  T.not_null (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a;
  fold (enum_i32_pts_to tag) a p x;
}

ghost fn enum_i32_pts_to_uninit_not_null (tag: string) (a: ptr)
  preserves (enum_i32_pts_to_uninit tag) a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold (enum_i32_pts_to_uninit tag) a;
  T.storage_not_null (enum_i32_ctype tag) (enum_i32_alignof tag) a;
  fold (enum_i32_pts_to_uninit tag) a;
}

[@@allow_ambiguous]
ghost fn enum_i32_agree (tag: string) (a: ptr) (#p1 #p2: perm) (#x #y: I32.t)
  preserves (enum_i32_pts_to tag) a p1 x
  preserves (enum_i32_pts_to tag) a p2 y
  ensures   pure (x == y)
{
  unfold (enum_i32_pts_to tag) a p1 x;
  unfold (enum_i32_pts_to tag) a p2 y;
  T.agree (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) (enum_i32_repr_injective tag) a;
  fold (enum_i32_pts_to tag) a p1 x;
  fold (enum_i32_pts_to tag) a p2 y;
}

ghost fn enum_i32_share (tag: string) (a: ptr) (#p: perm) (#x: I32.t)
  requires (enum_i32_pts_to tag) a p x
  ensures  (enum_i32_pts_to tag) a (p /. 2.0R) x ** (enum_i32_pts_to tag) a (p /. 2.0R) x
{
  unfold (enum_i32_pts_to tag) a p x;
  T.share (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a;
  fold (enum_i32_pts_to tag) a (p /. 2.0R) x;
  fold (enum_i32_pts_to tag) a (p /. 2.0R) x;
}

[@@allow_ambiguous]
ghost fn enum_i32_gather (tag: string) (a: ptr) (#p1 #p2: perm) (#x #y: I32.t)
  requires (enum_i32_pts_to tag) a p1 x ** (enum_i32_pts_to tag) a p2 y
  ensures  (enum_i32_pts_to tag) a (p1 +. p2) x ** pure (x == y)
{
  unfold (enum_i32_pts_to tag) a p1 x;
  unfold (enum_i32_pts_to tag) a p2 y;
  T.gather (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) (enum_i32_repr_injective tag) a;
  fold (enum_i32_pts_to tag) a (p1 +. p2) x;
}

ghost fn enum_i32_reveal (tag: string) (a: ptr) (#p: perm) (#x: I32.t)
  requires (enum_i32_pts_to tag) a p x
  ensures  exists* b e. mem_pts_to_at a p b e ** pure (ET.elen e == len b /\ ET.read_ok e (enum_i32_ctype tag) /\ (enum_i32_repr tag) x b /\ aligned a (enum_i32_alignof tag))
{
  unfold (enum_i32_pts_to tag) a p x;
  T.reveal_value (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a;
}

ghost fn enum_i32_conceal (tag: string) (a: ptr) (#p: perm) (#b: bytes) (#x: I32.t) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure ((enum_i32_repr tag) x b)
  requires pure (aligned a (enum_i32_alignof tag))
  requires pure (ET.elen e == len b /\ ET.read_ok e (enum_i32_ctype tag))
  ensures  (enum_i32_pts_to tag) a p x
{
  (enum_i32_repr_no_prov tag) x b;
  T.claim (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a #p #x #b #e;
  fold (enum_i32_pts_to tag) a p x;
}

ghost fn enum_i32_forget (tag: string) (a: ptr) (#x: I32.t)
  requires (enum_i32_pts_to tag) a 1.0R x
  ensures  (enum_i32_pts_to_uninit tag) a
{
  unfold (enum_i32_pts_to tag) a 1.0R x;
  T.forget (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a;
  fold (enum_i32_pts_to_uninit tag) a;
}

ghost fn enum_i32_claim (tag: string) (a: ptr) (#b: bytes) (x: I32.t) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure ((enum_i32_repr tag) x b)
  requires pure (aligned a (enum_i32_alignof tag))
  requires pure (ET.elen e == len b /\ ET.read_ok e (enum_i32_ctype tag))
  ensures  (enum_i32_pts_to tag) a 1.0R x
{
  (enum_i32_repr_no_prov tag) x b;
  T.claim (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a #1.0R #x #b #e;
  fold (enum_i32_pts_to tag) a 1.0R x;
}

ghost fn enum_i32_claim_uninit (tag: string) (a: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v (enum_i32_sizeof tag) /\ aligned a (enum_i32_alignof tag))
  requires pure (ET.elen e == len b /\ ET.read_ok e (enum_i32_ctype tag))
  ensures  (enum_i32_pts_to_uninit tag) a
{
  T.claim_storage (enum_i32_ctype tag) (enum_i32_alignof tag) a;
  fold (enum_i32_pts_to_uninit tag) a;
}

ghost fn enum_i32_reveal_uninit (tag: string) (a: ptr)
  requires (enum_i32_pts_to_uninit tag) a
  ensures  exists* b e. mem_pts_to_at a 1.0R b e ** pure (ET.elen e == len b /\ ET.read_ok e (enum_i32_ctype tag) /\ len b == SZ.v (enum_i32_sizeof tag) /\ aligned a (enum_i32_alignof tag))
{
  unfold (enum_i32_pts_to_uninit tag) a;
  T.reveal_storage (enum_i32_ctype tag) (enum_i32_alignof tag) a;
}

ghost fn enum_i32_of_elem (tag: string) (a: ptr) (#p: perm) (#x: I32.t)
  requires elem_pts_to (enum_i32_ctype tag) (enum_i32_repr tag) a p x
  requires pure (aligned a (enum_i32_alignof tag))
  ensures  (enum_i32_pts_to tag) a p x
{
  elem_reveal (enum_i32_ctype tag) (enum_i32_repr tag) a;
  (enum_i32_conceal tag) a #p #_ #x;
}

ghost fn enum_i32_to_elem (tag: string) (a: ptr) (#p: perm) (#x: I32.t)
  requires (enum_i32_pts_to tag) a p x
  ensures  elem_pts_to (enum_i32_ctype tag) (enum_i32_repr tag) a p x
  ensures  pure (aligned a (enum_i32_alignof tag))
{
  (enum_i32_reveal tag) a;
  elem_conceal (enum_i32_ctype tag) (enum_i32_repr tag) a #p #_ #x;
}

