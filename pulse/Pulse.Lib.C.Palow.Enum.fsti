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
open Pulse.Lib.C.Palow.Enum.Base


fn enum_u32_read (tag: string) (a: ptr) (#p: perm) (#x: erased U32.t)
  preserves (enum_u32_pts_to tag) a p x
  returns  y : U32.t
  ensures  rewrites_to y (reveal x)

fn enum_u32_write (tag: string) (a: ptr) (y: U32.t) (#x: erased U32.t)
  requires (enum_u32_pts_to tag) a 1.0R x
  ensures  (enum_u32_pts_to tag) a 1.0R y

fn enum_u32_write_uninit (tag: string) (a: ptr) (y: U32.t)
  requires (enum_u32_pts_to_uninit tag) a
  ensures  (enum_u32_pts_to tag) a 1.0R y

fn enum_u32_stack_alloc (tag: string) ()
  returns  a : ptr
  ensures  (enum_u32_pts_to_uninit tag) a
  ensures pure (fixed_metadata a (ET.etypes_of (enum_u32_ctype tag) true))

fn enum_u32_stack_free (tag: string) (a: ptr)
  requires (enum_u32_pts_to_uninit tag) a

fn enum_u32_read_at (tag: string) (a: ptr) (#p: perm) (#x: erased U32.t) (#e: ET.etypes)
  preserves V.value (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a p x e
  returns y: U32.t
  ensures rewrites_to y (reveal x)

fn enum_u32_write_at (tag: string) (a: ptr) (y: U32.t) (#x: erased U32.t)
    (#e: ET.etypes { ET.elen e == ET.csize (enum_u32_ctype tag) })
  requires V.value (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a 1.0R x e
  ensures V.value (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a 1.0R y (EM.store_index e (enum_u32_ctype tag))

fn enum_u32_write_uninit_at (tag: string) (a: ptr) (y: U32.t)
    (#e: ET.etypes { ET.elen e == ET.csize (enum_u32_ctype tag) })
  requires V.storage (enum_u32_ctype tag) (enum_u32_alignof tag) a e
  ensures V.value (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a 1.0R y (EM.store_index e (enum_u32_ctype tag))

fn enum_u32_write_existing (tag: string) (a: ptr) (y: U32.t)
    (#e: ET.etypes { ET.elen e == ET.csize (enum_u32_ctype tag) })
  requires V.storage (enum_u32_ctype tag) (enum_u32_alignof tag) a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a 1.0R y e

fn enum_u32_initialize_at (tag: string) (a: ptr) (y: U32.t)
  requires E.prepared a (enum_u32_ctype tag)
  requires pure (aligned a (enum_u32_alignof tag))
  ensures exists* e. V.value (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type (enum_u32_ctype tag)) ==> e == ET.etypes_of (enum_u32_ctype tag) false))

fn enum_u32_initialize (tag: string) (a: ptr) (y: U32.t)
  requires E.prepared a (enum_u32_ctype tag)
  requires pure (aligned a (enum_u32_alignof tag))
  ensures (enum_u32_pts_to tag) a 1.0R y

fn enum_i32_read (tag: string) (a: ptr) (#p: perm) (#x: erased I32.t)
  preserves (enum_i32_pts_to tag) a p x
  returns  y : I32.t
  ensures  rewrites_to y (reveal x)

fn enum_i32_write (tag: string) (a: ptr) (y: I32.t) (#x: erased I32.t)
  requires (enum_i32_pts_to tag) a 1.0R x
  ensures  (enum_i32_pts_to tag) a 1.0R y

fn enum_i32_write_uninit (tag: string) (a: ptr) (y: I32.t)
  requires (enum_i32_pts_to_uninit tag) a
  ensures  (enum_i32_pts_to tag) a 1.0R y

fn enum_i32_stack_alloc (tag: string) ()
  returns  a : ptr
  ensures  (enum_i32_pts_to_uninit tag) a
  ensures pure (fixed_metadata a (ET.etypes_of (enum_i32_ctype tag) true))

fn enum_i32_stack_free (tag: string) (a: ptr)
  requires (enum_i32_pts_to_uninit tag) a

fn enum_i32_read_at (tag: string) (a: ptr) (#p: perm) (#x: erased I32.t) (#e: ET.etypes)
  preserves V.value (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a p x e
  returns y: I32.t
  ensures rewrites_to y (reveal x)

fn enum_i32_write_at (tag: string) (a: ptr) (y: I32.t) (#x: erased I32.t)
    (#e: ET.etypes { ET.elen e == ET.csize (enum_i32_ctype tag) })
  requires V.value (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a 1.0R x e
  ensures V.value (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a 1.0R y (EM.store_index e (enum_i32_ctype tag))

fn enum_i32_write_uninit_at (tag: string) (a: ptr) (y: I32.t)
    (#e: ET.etypes { ET.elen e == ET.csize (enum_i32_ctype tag) })
  requires V.storage (enum_i32_ctype tag) (enum_i32_alignof tag) a e
  ensures V.value (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a 1.0R y (EM.store_index e (enum_i32_ctype tag))

fn enum_i32_write_existing (tag: string) (a: ptr) (y: I32.t)
    (#e: ET.etypes { ET.elen e == ET.csize (enum_i32_ctype tag) })
  requires V.storage (enum_i32_ctype tag) (enum_i32_alignof tag) a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a 1.0R y e

fn enum_i32_initialize_at (tag: string) (a: ptr) (y: I32.t)
  requires E.prepared a (enum_i32_ctype tag)
  requires pure (aligned a (enum_i32_alignof tag))
  ensures exists* e. V.value (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type (enum_i32_ctype tag)) ==> e == ET.etypes_of (enum_i32_ctype tag) false))

fn enum_i32_initialize (tag: string) (a: ptr) (y: I32.t)
  requires E.prepared a (enum_i32_ctype tag)
  requires pure (aligned a (enum_i32_alignof tag))
  ensures (enum_i32_pts_to tag) a 1.0R y

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

fn enum_u32_write_as_uint32_t (tag: string) (a: ptr) (y: U32.t) (#x: erased U32.t)
  requires (enum_u32_pts_to tag) a 1.0R x
  ensures  (enum_u32_pts_to tag) a 1.0R (y)

fn enum_u32_read_as_int32_t (tag: string) (a: ptr) (#p: perm) (#x: erased U32.t)
  preserves (enum_u32_pts_to tag) a p x
  returns  r : I32.t
  ensures  pure (r == FStar.Int.Cast.uint32_to_int32 (reveal x))

fn enum_u32_write_as_int32_t (tag: string) (a: ptr) (y: I32.t) (#x: erased U32.t)
  requires (enum_u32_pts_to tag) a 1.0R x
  ensures  (enum_u32_pts_to tag) a 1.0R (FStar.Int.Cast.int32_to_uint32 y)

fn enum_i32_read_as_int32_t (tag: string) (a: ptr) (#p: perm) (#x: erased I32.t)
  preserves (enum_i32_pts_to tag) a p x
  returns  r : I32.t
  ensures  pure (r == (reveal x))

fn enum_i32_write_as_int32_t (tag: string) (a: ptr) (y: I32.t) (#x: erased I32.t)
  requires (enum_i32_pts_to tag) a 1.0R x
  ensures  (enum_i32_pts_to tag) a 1.0R (y)

fn enum_i32_read_as_uint32_t (tag: string) (a: ptr) (#p: perm) (#x: erased I32.t)
  preserves (enum_i32_pts_to tag) a p x
  returns  r : U32.t
  ensures  pure (r == FStar.Int.Cast.int32_to_uint32 (reveal x))

fn enum_i32_write_as_uint32_t (tag: string) (a: ptr) (y: U32.t) (#x: erased I32.t)
  requires (enum_i32_pts_to tag) a 1.0R x
  ensures  (enum_i32_pts_to tag) a 1.0R (FStar.Int.Cast.uint32_to_int32 y)

