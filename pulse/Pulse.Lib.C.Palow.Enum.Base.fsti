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
module SZ = FStar.SizeT
module ET = Pulse.Lib.C.Palow.Etype
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64
open Pulse.Lib.C.Palow.CTypes


let enum_u32_sizeof (tag: string) : SZ.t = 4sz
let enum_u32_alignof (tag: string) : SZ.t = 4sz
let enum_u32_ctype (tag: string) : ET.ctype = ET.TScalar (ET.SEnum tag ET.SUInt32)

let enum_u32_repr (tag: string) (x: U32.t) (b: bytes) : prop =
  b == encode (SZ.v (enum_u32_sizeof tag)) None (U32.v x)

val enum_u32_pts_to (tag: string) ([@@@mkey] a: ptr) (p: perm) (x: U32.t) : slprop


val enum_u32_pts_to_uninit (tag: string) ([@@@mkey] a: ptr) : slprop


val enum_u32_repr_no_prov (tag: string) (x: U32.t) (b: bytes)
  : Lemma (requires (enum_u32_repr tag) x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v (enum_u32_sizeof tag))


val enum_u32_repr_injective (tag: string) (x y: U32.t) (b: bytes)
  : Lemma (requires (enum_u32_repr tag) x b /\ (enum_u32_repr tag) y b)
          (ensures  x == y)


ghost fn enum_u32_pts_to_not_null (tag: string) (a: ptr) (#p: perm) (#x: U32.t)
  preserves (enum_u32_pts_to tag) a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


ghost fn enum_u32_pts_to_uninit_not_null (tag: string) (a: ptr)
  preserves (enum_u32_pts_to_uninit tag) a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


[@@allow_ambiguous]
ghost fn enum_u32_agree (tag: string) (a: ptr) (#p1 #p2: perm) (#x #y: U32.t)
  preserves (enum_u32_pts_to tag) a p1 x
  preserves (enum_u32_pts_to tag) a p2 y
  ensures   pure (x == y)


ghost fn enum_u32_share (tag: string) (a: ptr) (#p: perm) (#x: U32.t)
  requires (enum_u32_pts_to tag) a p x
  ensures  (enum_u32_pts_to tag) a (p /. 2.0R) x ** (enum_u32_pts_to tag) a (p /. 2.0R) x


[@@allow_ambiguous]
ghost fn enum_u32_gather (tag: string) (a: ptr) (#p1 #p2: perm) (#x #y: U32.t)
  requires (enum_u32_pts_to tag) a p1 x ** (enum_u32_pts_to tag) a p2 y
  ensures  (enum_u32_pts_to tag) a (p1 +. p2) x ** pure (x == y)


ghost fn enum_u32_reveal (tag: string) (a: ptr) (#p: perm) (#x: U32.t)
  requires (enum_u32_pts_to tag) a p x
  ensures  exists* b e. mem_pts_to_at a p b e ** pure (ET.elen e == len b /\ ET.read_ok e (enum_u32_ctype tag) /\ (enum_u32_repr tag) x b /\ aligned a (enum_u32_alignof tag))


ghost fn enum_u32_conceal (tag: string) (a: ptr) (#p: perm) (#b: bytes) (#x: U32.t) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure ((enum_u32_repr tag) x b)
  requires pure (aligned a (enum_u32_alignof tag))
  requires pure (ET.elen e == len b /\ ET.read_ok e (enum_u32_ctype tag))
  ensures  (enum_u32_pts_to tag) a p x


ghost fn enum_u32_forget (tag: string) (a: ptr) (#x: U32.t)
  requires (enum_u32_pts_to tag) a 1.0R x
  ensures  (enum_u32_pts_to_uninit tag) a


ghost fn enum_u32_claim (tag: string) (a: ptr) (#b: bytes) (x: U32.t) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure ((enum_u32_repr tag) x b)
  requires pure (aligned a (enum_u32_alignof tag))
  requires pure (ET.elen e == len b /\ ET.read_ok e (enum_u32_ctype tag))
  ensures  (enum_u32_pts_to tag) a 1.0R x

ghost fn enum_u32_claim_uninit (tag: string) (a: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v (enum_u32_sizeof tag) /\ aligned a (enum_u32_alignof tag))
  requires pure (ET.elen e == len b /\ ET.read_ok e (enum_u32_ctype tag))
  ensures  (enum_u32_pts_to_uninit tag) a


ghost fn enum_u32_reveal_uninit (tag: string) (a: ptr)
  requires (enum_u32_pts_to_uninit tag) a
  ensures  exists* b e. mem_pts_to_at a 1.0R b e ** pure (ET.elen e == len b /\ ET.read_ok e (enum_u32_ctype tag) /\ len b == SZ.v (enum_u32_sizeof tag) /\ aligned a (enum_u32_alignof tag))



ghost fn enum_u32_of_elem (tag: string) (a: ptr) (#p: perm) (#x: U32.t)
  requires elem_pts_to (enum_u32_ctype tag) (enum_u32_repr tag) a p x
  requires pure (aligned a (enum_u32_alignof tag))
  ensures  (enum_u32_pts_to tag) a p x


ghost fn enum_u32_to_elem (tag: string) (a: ptr) (#p: perm) (#x: U32.t)
  requires (enum_u32_pts_to tag) a p x
  ensures  elem_pts_to (enum_u32_ctype tag) (enum_u32_repr tag) a p x
  ensures  pure (aligned a (enum_u32_alignof tag))


let enum_u32_repr_len (tag: string) (x: U32.t) (b: bytes)
  : Lemma (requires (enum_u32_repr tag) x b) (ensures len b == SZ.v (enum_u32_sizeof tag))
  = (enum_u32_repr_no_prov tag) x b

let enum_i32_sizeof (tag: string) : SZ.t = 4sz
let enum_i32_alignof (tag: string) : SZ.t = 4sz
let enum_i32_ctype (tag: string) : ET.ctype = ET.TScalar (ET.SEnum tag ET.SInt32)

let enum_i32_repr (tag: string) (x: I32.t) (b: bytes) : prop =
  b == encode (SZ.v (enum_i32_sizeof tag)) None (to_bits 32 (I32.v x))

val enum_i32_pts_to (tag: string) ([@@@mkey] a: ptr) (p: perm) (x: I32.t) : slprop


val enum_i32_pts_to_uninit (tag: string) ([@@@mkey] a: ptr) : slprop


val enum_i32_repr_no_prov (tag: string) (x: I32.t) (b: bytes)
  : Lemma (requires (enum_i32_repr tag) x b)
          (ensures  no_prov b /\ initialized b /\ len b == SZ.v (enum_i32_sizeof tag))


val enum_i32_repr_injective (tag: string) (x y: I32.t) (b: bytes)
  : Lemma (requires (enum_i32_repr tag) x b /\ (enum_i32_repr tag) y b)
          (ensures  x == y)


ghost fn enum_i32_pts_to_not_null (tag: string) (a: ptr) (#p: perm) (#x: I32.t)
  preserves (enum_i32_pts_to tag) a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


ghost fn enum_i32_pts_to_uninit_not_null (tag: string) (a: ptr)
  preserves (enum_i32_pts_to_uninit tag) a
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


[@@allow_ambiguous]
ghost fn enum_i32_agree (tag: string) (a: ptr) (#p1 #p2: perm) (#x #y: I32.t)
  preserves (enum_i32_pts_to tag) a p1 x
  preserves (enum_i32_pts_to tag) a p2 y
  ensures   pure (x == y)


ghost fn enum_i32_share (tag: string) (a: ptr) (#p: perm) (#x: I32.t)
  requires (enum_i32_pts_to tag) a p x
  ensures  (enum_i32_pts_to tag) a (p /. 2.0R) x ** (enum_i32_pts_to tag) a (p /. 2.0R) x


[@@allow_ambiguous]
ghost fn enum_i32_gather (tag: string) (a: ptr) (#p1 #p2: perm) (#x #y: I32.t)
  requires (enum_i32_pts_to tag) a p1 x ** (enum_i32_pts_to tag) a p2 y
  ensures  (enum_i32_pts_to tag) a (p1 +. p2) x ** pure (x == y)


ghost fn enum_i32_reveal (tag: string) (a: ptr) (#p: perm) (#x: I32.t)
  requires (enum_i32_pts_to tag) a p x
  ensures  exists* b e. mem_pts_to_at a p b e ** pure (ET.elen e == len b /\ ET.read_ok e (enum_i32_ctype tag) /\ (enum_i32_repr tag) x b /\ aligned a (enum_i32_alignof tag))


ghost fn enum_i32_conceal (tag: string) (a: ptr) (#p: perm) (#b: bytes) (#x: I32.t) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure ((enum_i32_repr tag) x b)
  requires pure (aligned a (enum_i32_alignof tag))
  requires pure (ET.elen e == len b /\ ET.read_ok e (enum_i32_ctype tag))
  ensures  (enum_i32_pts_to tag) a p x


ghost fn enum_i32_forget (tag: string) (a: ptr) (#x: I32.t)
  requires (enum_i32_pts_to tag) a 1.0R x
  ensures  (enum_i32_pts_to_uninit tag) a


ghost fn enum_i32_claim (tag: string) (a: ptr) (#b: bytes) (x: I32.t) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure ((enum_i32_repr tag) x b)
  requires pure (aligned a (enum_i32_alignof tag))
  requires pure (ET.elen e == len b /\ ET.read_ok e (enum_i32_ctype tag))
  ensures  (enum_i32_pts_to tag) a 1.0R x

ghost fn enum_i32_claim_uninit (tag: string) (a: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v (enum_i32_sizeof tag) /\ aligned a (enum_i32_alignof tag))
  requires pure (ET.elen e == len b /\ ET.read_ok e (enum_i32_ctype tag))
  ensures  (enum_i32_pts_to_uninit tag) a


ghost fn enum_i32_reveal_uninit (tag: string) (a: ptr)
  requires (enum_i32_pts_to_uninit tag) a
  ensures  exists* b e. mem_pts_to_at a 1.0R b e ** pure (ET.elen e == len b /\ ET.read_ok e (enum_i32_ctype tag) /\ len b == SZ.v (enum_i32_sizeof tag) /\ aligned a (enum_i32_alignof tag))



ghost fn enum_i32_of_elem (tag: string) (a: ptr) (#p: perm) (#x: I32.t)
  requires elem_pts_to (enum_i32_ctype tag) (enum_i32_repr tag) a p x
  requires pure (aligned a (enum_i32_alignof tag))
  ensures  (enum_i32_pts_to tag) a p x


ghost fn enum_i32_to_elem (tag: string) (a: ptr) (#p: perm) (#x: I32.t)
  requires (enum_i32_pts_to tag) a p x
  ensures  elem_pts_to (enum_i32_ctype tag) (enum_i32_repr tag) a p x
  ensures  pure (aligned a (enum_i32_alignof tag))


let enum_i32_repr_len (tag: string) (x: I32.t) (b: bytes)
  : Lemma (requires (enum_i32_repr tag) x b) (ensures len b == SZ.v (enum_i32_sizeof tag))
  = (enum_i32_repr_no_prov tag) x b

