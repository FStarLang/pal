module Pulse.Lib.C.Palow.Enum

(* Enumerated types (6.7.2.2). An enumerated type has the size, alignment and
   representation of its underlying integer type, here `unsigned int` or
   `int`, but it is a distinct type: its effective-type descriptor is
   `ET.SEnum tag base`, so two different enumerated types do not alias each
   other while either one may still be accessed through its underlying type or
   that type's signed/unsigned counterpart (6.5p7).

   One family per underlying type, parameterized by the enumeration's tag.
   PAL emits, per enumeration, an `Enum_<tag>` module of `unfold` aliases
   (`enum_u32_color_read = enum_u32_read "color"`, ...).

   Generated from the 16-bit blocks of Pulse.Lib.C.Palow.Machine. *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Encoding
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.Float
open Pulse.Lib.C.Palow.CTypes
module ET = Pulse.Lib.C.Palow.Etype
module EM = Pulse.Lib.C.Palow.Effective.Machine
module V = Pulse.Lib.C.Palow.Effective.Value
module E = Pulse.Lib.C.Palow.Effective
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64
module I = Pulse.Lib.C.Palow.Machine.Intrinsics
module Enc = Pulse.Lib.C.Palow.Encoding
open Pulse.Lib.C.Palow.Enum.Base
module EI = Pulse.Lib.C.Palow.Enum.Intrinsics


fn enum_u32_read (tag: string) (a: ptr) (#p: perm) (#x: erased U32.t)
  preserves (enum_u32_pts_to tag) a p x
  returns  y : U32.t
  ensures  rewrites_to y (reveal x)
{
  (enum_u32_reveal tag) a;
  with b e. assert (mem_pts_to_at a p b e);
  (enum_u32_repr_no_prov tag) (reveal x) b;
  let y = (EI.enum_u32_read_at tag) a #p #x #(hide b) #e;
  (enum_u32_conceal tag) a #p #b #(reveal x) #e;
  y
}

fn enum_u32_write (tag: string) (a: ptr) (y: U32.t) (#x: erased U32.t)
  requires (enum_u32_pts_to tag) a 1.0R x
  ensures  (enum_u32_pts_to tag) a 1.0R y
{
  (enum_u32_reveal tag) a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v (enum_u32_sizeof tag)) None (U32.v y);
  (enum_u32_repr_no_prov tag) y b;
  EM.store a (hide (enum_u32_ctype tag)) b;
  ET.store_read_ok e (enum_u32_ctype tag);
  (enum_u32_conceal tag) a #1.0R #b #y #(EM.store_index e (enum_u32_ctype tag))
}

fn enum_u32_write_uninit (tag: string) (a: ptr) (y: U32.t)
  requires (enum_u32_pts_to_uninit tag) a
  ensures  (enum_u32_pts_to tag) a 1.0R y
{
  (enum_u32_reveal_uninit tag) a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v (enum_u32_sizeof tag)) None (U32.v y);
  (enum_u32_repr_no_prov tag) y b;
  EM.store a (hide (enum_u32_ctype tag)) b;
  ET.store_read_ok e (enum_u32_ctype tag);
  (enum_u32_conceal tag) a #1.0R #b #y #(EM.store_index e (enum_u32_ctype tag))
}

fn enum_u32_stack_alloc (tag: string) ()
  returns  a : ptr
  ensures  (enum_u32_pts_to_uninit tag) a
  ensures pure (fixed_metadata a (ET.etypes_of (enum_u32_ctype tag) true))
{
  let a = EM.stack_alloc (enum_u32_sizeof tag) (hide (enum_u32_ctype tag));
  aligned_divides a max_align (enum_u32_alignof tag);
  (enum_u32_claim_uninit tag) a;
  a
}

fn enum_u32_stack_free (tag: string) (a: ptr)
  requires (enum_u32_pts_to_uninit tag) a
{
  (EI.enum_u32_stack_free tag) a
}

fn enum_u32_read_at (tag: string) (a: ptr) (#p: perm) (#x: erased U32.t) (#e: ET.etypes)
  preserves V.value (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a p x e
  returns y: U32.t
  ensures rewrites_to y (reveal x)
{
  V.reveal_value (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a;
  with b. assert (mem_pts_to_at a p b e);
  (enum_u32_repr_no_prov tag) (reveal x) b;
  let y = (EI.enum_u32_read_at tag) a #p #x #(hide b) #e;
  V.claim (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a #p #(reveal x) #b #e;
  y
}

fn enum_u32_write_at (tag: string) (a: ptr) (y: U32.t) (#x: erased U32.t)
    (#e: ET.etypes { ET.elen e == ET.csize (enum_u32_ctype tag) })
  requires V.value (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a 1.0R x e
  ensures V.value (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a 1.0R y (EM.store_index e (enum_u32_ctype tag))
{
  V.reveal_value (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v (enum_u32_sizeof tag)) None (U32.v y);
  (enum_u32_repr_no_prov tag) y b;
  EM.store a (hide (enum_u32_ctype tag)) b;
  ET.store_read_ok e (enum_u32_ctype tag);
  V.claim (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a #1.0R #y #b #(EM.store_index e (enum_u32_ctype tag))
}

fn enum_u32_write_uninit_at (tag: string) (a: ptr) (y: U32.t)
    (#e: ET.etypes { ET.elen e == ET.csize (enum_u32_ctype tag) })
  requires V.storage (enum_u32_ctype tag) (enum_u32_alignof tag) a e
  ensures V.value (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a 1.0R y (EM.store_index e (enum_u32_ctype tag))
{
  V.reveal_storage (enum_u32_ctype tag) (enum_u32_alignof tag) a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v (enum_u32_sizeof tag)) None (U32.v y);
  (enum_u32_repr_no_prov tag) y b;
  EM.store a (hide (enum_u32_ctype tag)) b;
  ET.store_read_ok e (enum_u32_ctype tag);
  V.claim (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a #1.0R #y #b #(EM.store_index e (enum_u32_ctype tag))
}

fn enum_u32_write_existing (tag: string) (a: ptr) (y: U32.t)
    (#e: ET.etypes { ET.elen e == ET.csize (enum_u32_ctype tag) })
  requires V.storage (enum_u32_ctype tag) (enum_u32_alignof tag) a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a 1.0R y e
{
  V.reveal_storage (enum_u32_ctype tag) (enum_u32_alignof tag) a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  ET.store_readable_stable e (enum_u32_ctype tag);
  V.claim_storage (enum_u32_ctype tag) (enum_u32_alignof tag) a;
  (enum_u32_write_uninit_at tag) a y;
}

fn enum_u32_initialize_at (tag: string) (a: ptr) (y: U32.t)
  requires E.prepared a (enum_u32_ctype tag)
  requires pure (aligned a (enum_u32_alignof tag))
  ensures exists* e. V.value (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type (enum_u32_ctype tag)) ==> e == ET.etypes_of (enum_u32_ctype tag) false))
{
  let b = Enc.encode (SZ.v (enum_u32_sizeof tag)) None (U32.v y);
  (enum_u32_repr_no_prov tag) y b;
  EM.initialize a (hide (enum_u32_ctype tag)) b;
  with e. assert (mem_pts_to_at a 1.0R b e);
  V.claim (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a #1.0R #y #b #e;
}

fn enum_u32_initialize (tag: string) (a: ptr) (y: U32.t)
  requires E.prepared a (enum_u32_ctype tag)
  requires pure (aligned a (enum_u32_alignof tag))
  ensures (enum_u32_pts_to tag) a 1.0R y
{
  (enum_u32_initialize_at tag) a y;
  with e. assert (V.value (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a 1.0R y e);
  V.reveal_value (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a;
  with b. assert (mem_pts_to_at a 1.0R b e);
  (enum_u32_conceal tag) a #1.0R #b #y #e;
}

fn enum_i32_read (tag: string) (a: ptr) (#p: perm) (#x: erased I32.t)
  preserves (enum_i32_pts_to tag) a p x
  returns  y : I32.t
  ensures  rewrites_to y (reveal x)
{
  (enum_i32_reveal tag) a;
  with b e. assert (mem_pts_to_at a p b e);
  (enum_i32_repr_no_prov tag) (reveal x) b;
  let y = (EI.enum_i32_read_at tag) a #p #x #(hide b) #e;
  (enum_i32_conceal tag) a #p #b #(reveal x) #e;
  y
}

fn enum_i32_write (tag: string) (a: ptr) (y: I32.t) (#x: erased I32.t)
  requires (enum_i32_pts_to tag) a 1.0R x
  ensures  (enum_i32_pts_to tag) a 1.0R y
{
  (enum_i32_reveal tag) a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v (enum_i32_sizeof tag)) None (to_bits 32 (I32.v y));
  (enum_i32_repr_no_prov tag) y b;
  EM.store a (hide (enum_i32_ctype tag)) b;
  ET.store_read_ok e (enum_i32_ctype tag);
  (enum_i32_conceal tag) a #1.0R #b #y #(EM.store_index e (enum_i32_ctype tag))
}

fn enum_i32_write_uninit (tag: string) (a: ptr) (y: I32.t)
  requires (enum_i32_pts_to_uninit tag) a
  ensures  (enum_i32_pts_to tag) a 1.0R y
{
  (enum_i32_reveal_uninit tag) a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v (enum_i32_sizeof tag)) None (to_bits 32 (I32.v y));
  (enum_i32_repr_no_prov tag) y b;
  EM.store a (hide (enum_i32_ctype tag)) b;
  ET.store_read_ok e (enum_i32_ctype tag);
  (enum_i32_conceal tag) a #1.0R #b #y #(EM.store_index e (enum_i32_ctype tag))
}

fn enum_i32_stack_alloc (tag: string) ()
  returns  a : ptr
  ensures  (enum_i32_pts_to_uninit tag) a
  ensures pure (fixed_metadata a (ET.etypes_of (enum_i32_ctype tag) true))
{
  let a = EM.stack_alloc (enum_i32_sizeof tag) (hide (enum_i32_ctype tag));
  aligned_divides a max_align (enum_i32_alignof tag);
  (enum_i32_claim_uninit tag) a;
  a
}

fn enum_i32_stack_free (tag: string) (a: ptr)
  requires (enum_i32_pts_to_uninit tag) a
{
  (EI.enum_i32_stack_free tag) a
}

fn enum_i32_read_at (tag: string) (a: ptr) (#p: perm) (#x: erased I32.t) (#e: ET.etypes)
  preserves V.value (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a p x e
  returns y: I32.t
  ensures rewrites_to y (reveal x)
{
  V.reveal_value (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a;
  with b. assert (mem_pts_to_at a p b e);
  (enum_i32_repr_no_prov tag) (reveal x) b;
  let y = (EI.enum_i32_read_at tag) a #p #x #(hide b) #e;
  V.claim (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a #p #(reveal x) #b #e;
  y
}

fn enum_i32_write_at (tag: string) (a: ptr) (y: I32.t) (#x: erased I32.t)
    (#e: ET.etypes { ET.elen e == ET.csize (enum_i32_ctype tag) })
  requires V.value (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a 1.0R x e
  ensures V.value (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a 1.0R y (EM.store_index e (enum_i32_ctype tag))
{
  V.reveal_value (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v (enum_i32_sizeof tag)) None (to_bits 32 (I32.v y));
  (enum_i32_repr_no_prov tag) y b;
  EM.store a (hide (enum_i32_ctype tag)) b;
  ET.store_read_ok e (enum_i32_ctype tag);
  V.claim (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a #1.0R #y #b #(EM.store_index e (enum_i32_ctype tag))
}

fn enum_i32_write_uninit_at (tag: string) (a: ptr) (y: I32.t)
    (#e: ET.etypes { ET.elen e == ET.csize (enum_i32_ctype tag) })
  requires V.storage (enum_i32_ctype tag) (enum_i32_alignof tag) a e
  ensures V.value (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a 1.0R y (EM.store_index e (enum_i32_ctype tag))
{
  V.reveal_storage (enum_i32_ctype tag) (enum_i32_alignof tag) a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v (enum_i32_sizeof tag)) None (to_bits 32 (I32.v y));
  (enum_i32_repr_no_prov tag) y b;
  EM.store a (hide (enum_i32_ctype tag)) b;
  ET.store_read_ok e (enum_i32_ctype tag);
  V.claim (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a #1.0R #y #b #(EM.store_index e (enum_i32_ctype tag))
}

fn enum_i32_write_existing (tag: string) (a: ptr) (y: I32.t)
    (#e: ET.etypes { ET.elen e == ET.csize (enum_i32_ctype tag) })
  requires V.storage (enum_i32_ctype tag) (enum_i32_alignof tag) a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a 1.0R y e
{
  V.reveal_storage (enum_i32_ctype tag) (enum_i32_alignof tag) a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  ET.store_readable_stable e (enum_i32_ctype tag);
  V.claim_storage (enum_i32_ctype tag) (enum_i32_alignof tag) a;
  (enum_i32_write_uninit_at tag) a y;
}

fn enum_i32_initialize_at (tag: string) (a: ptr) (y: I32.t)
  requires E.prepared a (enum_i32_ctype tag)
  requires pure (aligned a (enum_i32_alignof tag))
  ensures exists* e. V.value (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type (enum_i32_ctype tag)) ==> e == ET.etypes_of (enum_i32_ctype tag) false))
{
  let b = Enc.encode (SZ.v (enum_i32_sizeof tag)) None (to_bits 32 (I32.v y));
  (enum_i32_repr_no_prov tag) y b;
  EM.initialize a (hide (enum_i32_ctype tag)) b;
  with e. assert (mem_pts_to_at a 1.0R b e);
  V.claim (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a #1.0R #y #b #e;
}

fn enum_i32_initialize (tag: string) (a: ptr) (y: I32.t)
  requires E.prepared a (enum_i32_ctype tag)
  requires pure (aligned a (enum_i32_alignof tag))
  ensures (enum_i32_pts_to tag) a 1.0R y
{
  (enum_i32_initialize_at tag) a y;
  with e. assert (V.value (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a 1.0R y e);
  V.reveal_value (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a;
  with b. assert (mem_pts_to_at a 1.0R b e);
  (enum_i32_conceal tag) a #1.0R #b #y #e;
}

(* Access through the underlying integer type or its signed/unsigned
   counterpart. Both are compatible lvalues for an enumerated object (6.5p7),
   and the object's effective type stays the enumeration: a declared object's
   type never changes, and the bytes are those of the underlying type. The
   reverse direction (the underlying type viewed as an enumeration) is not
   offered, since compatibility is not transitive. *)

fn enum_u32_read_as_uint32_t (tag: string) (a: ptr) (#p: perm) (#x: erased U32.t)
  preserves (enum_u32_pts_to tag) a p x
  returns  r : U32.t
  ensures  pure (r == (reveal x))
{
  let v = enum_u32_read tag a;
  v
}

fn enum_u32_write_as_uint32_t (tag: string) (a: ptr) (y: U32.t) (#x: erased U32.t)
  requires (enum_u32_pts_to tag) a 1.0R x
  ensures  (enum_u32_pts_to tag) a 1.0R (y)
{
  enum_u32_write tag a (y)
}

fn enum_u32_read_as_int32_t (tag: string) (a: ptr) (#p: perm) (#x: erased U32.t)
  preserves (enum_u32_pts_to tag) a p x
  returns  r : I32.t
  ensures  pure (r == FStar.Int.Cast.uint32_to_int32 (reveal x))
{
  let v = enum_u32_read tag a;
  FStar.Int.Cast.uint32_to_int32 v
}

fn enum_u32_write_as_int32_t (tag: string) (a: ptr) (y: I32.t) (#x: erased U32.t)
  requires (enum_u32_pts_to tag) a 1.0R x
  ensures  (enum_u32_pts_to tag) a 1.0R (FStar.Int.Cast.int32_to_uint32 y)
{
  enum_u32_write tag a (FStar.Int.Cast.int32_to_uint32 y)
}

fn enum_i32_read_as_int32_t (tag: string) (a: ptr) (#p: perm) (#x: erased I32.t)
  preserves (enum_i32_pts_to tag) a p x
  returns  r : I32.t
  ensures  pure (r == (reveal x))
{
  let v = enum_i32_read tag a;
  v
}

fn enum_i32_write_as_int32_t (tag: string) (a: ptr) (y: I32.t) (#x: erased I32.t)
  requires (enum_i32_pts_to tag) a 1.0R x
  ensures  (enum_i32_pts_to tag) a 1.0R (y)
{
  enum_i32_write tag a (y)
}

fn enum_i32_read_as_uint32_t (tag: string) (a: ptr) (#p: perm) (#x: erased I32.t)
  preserves (enum_i32_pts_to tag) a p x
  returns  r : U32.t
  ensures  pure (r == FStar.Int.Cast.int32_to_uint32 (reveal x))
{
  let v = enum_i32_read tag a;
  FStar.Int.Cast.int32_to_uint32 v
}

fn enum_i32_write_as_uint32_t (tag: string) (a: ptr) (y: U32.t) (#x: erased I32.t)
  requires (enum_i32_pts_to tag) a 1.0R x
  ensures  (enum_i32_pts_to tag) a 1.0R (FStar.Int.Cast.uint32_to_int32 y)
{
  enum_i32_write tag a (FStar.Int.Cast.uint32_to_int32 y)
}

