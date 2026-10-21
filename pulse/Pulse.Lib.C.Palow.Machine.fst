module Pulse.Lib.C.Palow.Machine

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

fn uint32_t_read (a: ptr) (#p: perm) (#x: erased U32.t)
  preserves uint32_t_pts_to a p x
  returns  y : U32.t
  ensures  rewrites_to y (reveal x)
{
  uint32_t_reveal a;
  with b e. assert (mem_pts_to_at a p b e);
  uint32_t_repr_no_prov (reveal x) b;
  let y = I.uint32_t_read_at a #p #x #(hide b) #e;
  uint32_t_conceal a #p #b #(reveal x) #e;
  y
}

fn uint32_t_write (a: ptr) (y: U32.t) (#x: erased U32.t)
  requires uint32_t_pts_to a 1.0R x
  ensures  uint32_t_pts_to a 1.0R y
{
  uint32_t_reveal a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint32_t_sizeof) None (U32.v y);
  uint32_t_repr_no_prov y b;
  EM.store a (hide uint32_t_ctype) b;
  ET.store_read_ok e uint32_t_ctype;
  uint32_t_conceal a #1.0R #b #y #(EM.store_index e uint32_t_ctype)
}

fn uint32_t_write_uninit (a: ptr) (y: U32.t)
  requires uint32_t_pts_to_uninit a
  ensures  uint32_t_pts_to a 1.0R y
{
  uint32_t_reveal_uninit a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint32_t_sizeof) None (U32.v y);
  uint32_t_repr_no_prov y b;
  EM.store a (hide uint32_t_ctype) b;
  ET.store_read_ok e uint32_t_ctype;
  uint32_t_conceal a #1.0R #b #y #(EM.store_index e uint32_t_ctype)
}

fn uint8_t_read (a: ptr) (#p: perm) (#x: erased U8.t)
  preserves uint8_t_pts_to a p x
  returns  y : U8.t
  ensures  rewrites_to y (reveal x)
{
  uint8_t_reveal a;
  with b e. assert (mem_pts_to_at a p b e);
  uint8_t_repr_no_prov (reveal x) b;
  let y = I.uint8_t_read_at a #p #x #(hide b) #e;
  uint8_t_conceal a #p #b #(reveal x) #e;
  y
}

fn uint8_t_write (a: ptr) (y: U8.t) (#x: erased U8.t)
  requires uint8_t_pts_to a 1.0R x
  ensures  uint8_t_pts_to a 1.0R y
{
  uint8_t_reveal a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint8_t_sizeof) None (U8.v y);
  uint8_t_repr_no_prov y b;
  EM.store a (hide uint8_t_ctype) b;
  ET.store_read_ok e uint8_t_ctype;
  uint8_t_conceal a #1.0R #b #y #(EM.store_index e uint8_t_ctype)
}

fn ptr_read (a: ptr) (#p: perm) (#x: erased ptr)
  preserves ptr_pts_to a p x
  returns  y : ptr
  ensures  rewrites_to y (reveal x)
{
  ptr_reveal a;
  with b e. assert (mem_pts_to_at a p b e);
  ptr_repr_len (reveal x) b;
  let y = I.ptr_read_at a #p #x #(hide b) #e;
  ptr_conceal a #p #b #(reveal x) #e;
  y
}

fn ptr_write (a: ptr) (y: ptr) (#x: erased ptr)
  requires ptr_pts_to a 1.0R x
  ensures  ptr_pts_to a 1.0R y
{
  ptr_reveal a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  I.ptr_store a y;
  ET.store_read_ok e ptr_ctype;
  ptr_conceal a #1.0R #(Enc.encode (SZ.v ptr_sizeof) (prov_of y) (addr_of y)) #y #(EM.store_index e ptr_ctype)
}

fn uint32_t_stack_alloc ()
  returns  a : ptr
  ensures  uint32_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of uint32_t_ctype true))
{
  let a = EM.stack_alloc uint32_t_sizeof (hide uint32_t_ctype);
  aligned_divides a max_align uint32_t_alignof;
  uint32_t_claim_uninit a;
  a
}

fn uint32_t_stack_free (a: ptr)
  requires uint32_t_pts_to_uninit a
{
  I.uint32_t_stack_free a
}

fn ptr_write_uninit (a: ptr) (y: ptr)
  requires ptr_pts_to_uninit a
  ensures  ptr_pts_to a 1.0R y
{
  ptr_reveal_uninit a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  I.ptr_store a y;
  ET.store_read_ok e ptr_ctype;
  ptr_conceal a #1.0R #(Enc.encode (SZ.v ptr_sizeof) (prov_of y) (addr_of y)) #y #(EM.store_index e ptr_ctype)
}

fn ptr_stack_alloc ()
  returns  a : ptr
  ensures  ptr_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of ptr_ctype true))
{
  let a = EM.stack_alloc ptr_sizeof (hide ptr_ctype);
  aligned_divides a max_align ptr_alignof;
  ptr_claim_uninit a;
  a
}

fn ptr_stack_free (a: ptr)
  requires ptr_pts_to_uninit a
{
  I.ptr_stack_free a
}

fn bool_t_read (a: ptr) (#p: perm) (#x: erased bool)
  preserves bool_t_pts_to a p x
  returns  y : bool
  ensures  rewrites_to y (reveal x)
{
  bool_t_reveal a;
  with b e. assert (mem_pts_to_at a p b e);
  bool_t_repr_no_prov (reveal x) b;
  let y = I.bool_t_read_at a #p #x #(hide b) #e;
  bool_t_conceal a #p #b #(reveal x) #e;
  y
}

fn bool_t_write (a: ptr) (y: bool) (#x: erased bool)
  requires bool_t_pts_to a 1.0R x
  ensures  bool_t_pts_to a 1.0R y
{
  bool_t_reveal a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v bool_t_sizeof) None (if y then 1 else 0);
  bool_t_repr_no_prov y b;
  EM.store a (hide bool_t_ctype) b;
  ET.store_read_ok e bool_t_ctype;
  bool_t_conceal a #1.0R #b #y #(EM.store_index e bool_t_ctype)
}

fn bool_t_write_uninit (a: ptr) (y: bool)
  requires bool_t_pts_to_uninit a
  ensures  bool_t_pts_to a 1.0R y
{
  bool_t_reveal_uninit a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v bool_t_sizeof) None (if y then 1 else 0);
  bool_t_repr_no_prov y b;
  EM.store a (hide bool_t_ctype) b;
  ET.store_read_ok e bool_t_ctype;
  bool_t_conceal a #1.0R #b #y #(EM.store_index e bool_t_ctype)
}

fn bool_t_stack_alloc ()
  returns  a : ptr
  ensures  bool_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of bool_t_ctype true))
{
  let a = EM.stack_alloc bool_t_sizeof (hide bool_t_ctype);
  aligned_divides a max_align bool_t_alignof;
  bool_t_claim_uninit a;
  a
}

fn bool_t_stack_free (a: ptr)
  requires bool_t_pts_to_uninit a
{
  I.bool_t_stack_free a
}

fn int8_t_read (a: ptr) (#p: perm) (#x: erased I8.t)
  preserves int8_t_pts_to a p x
  returns  y : I8.t
  ensures  rewrites_to y (reveal x)
{
  int8_t_reveal a;
  with b e. assert (mem_pts_to_at a p b e);
  int8_t_repr_no_prov (reveal x) b;
  let y = I.int8_t_read_at a #p #x #(hide b) #e;
  int8_t_conceal a #p #b #(reveal x) #e;
  y
}

fn int8_t_write (a: ptr) (y: I8.t) (#x: erased I8.t)
  requires int8_t_pts_to a 1.0R x
  ensures  int8_t_pts_to a 1.0R y
{
  int8_t_reveal a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int8_t_sizeof) None (to_bits 8 (I8.v y));
  int8_t_repr_no_prov y b;
  EM.store a (hide int8_t_ctype) b;
  ET.store_read_ok e int8_t_ctype;
  int8_t_conceal a #1.0R #b #y #(EM.store_index e int8_t_ctype)
}

fn int8_t_write_uninit (a: ptr) (y: I8.t)
  requires int8_t_pts_to_uninit a
  ensures  int8_t_pts_to a 1.0R y
{
  int8_t_reveal_uninit a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int8_t_sizeof) None (to_bits 8 (I8.v y));
  int8_t_repr_no_prov y b;
  EM.store a (hide int8_t_ctype) b;
  ET.store_read_ok e int8_t_ctype;
  int8_t_conceal a #1.0R #b #y #(EM.store_index e int8_t_ctype)
}

fn int8_t_stack_alloc ()
  returns  a : ptr
  ensures  int8_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of int8_t_ctype true))
{
  let a = EM.stack_alloc int8_t_sizeof (hide int8_t_ctype);
  aligned_divides a max_align int8_t_alignof;
  int8_t_claim_uninit a;
  a
}

fn int8_t_stack_free (a: ptr)
  requires int8_t_pts_to_uninit a
{
  I.int8_t_stack_free a
}

fn int16_t_read (a: ptr) (#p: perm) (#x: erased I16.t)
  preserves int16_t_pts_to a p x
  returns  y : I16.t
  ensures  rewrites_to y (reveal x)
{
  int16_t_reveal a;
  with b e. assert (mem_pts_to_at a p b e);
  int16_t_repr_no_prov (reveal x) b;
  let y = I.int16_t_read_at a #p #x #(hide b) #e;
  int16_t_conceal a #p #b #(reveal x) #e;
  y
}

fn int16_t_write (a: ptr) (y: I16.t) (#x: erased I16.t)
  requires int16_t_pts_to a 1.0R x
  ensures  int16_t_pts_to a 1.0R y
{
  int16_t_reveal a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int16_t_sizeof) None (to_bits 16 (I16.v y));
  int16_t_repr_no_prov y b;
  EM.store a (hide int16_t_ctype) b;
  ET.store_read_ok e int16_t_ctype;
  int16_t_conceal a #1.0R #b #y #(EM.store_index e int16_t_ctype)
}

fn int16_t_write_uninit (a: ptr) (y: I16.t)
  requires int16_t_pts_to_uninit a
  ensures  int16_t_pts_to a 1.0R y
{
  int16_t_reveal_uninit a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int16_t_sizeof) None (to_bits 16 (I16.v y));
  int16_t_repr_no_prov y b;
  EM.store a (hide int16_t_ctype) b;
  ET.store_read_ok e int16_t_ctype;
  int16_t_conceal a #1.0R #b #y #(EM.store_index e int16_t_ctype)
}

fn int16_t_stack_alloc ()
  returns  a : ptr
  ensures  int16_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of int16_t_ctype true))
{
  let a = EM.stack_alloc int16_t_sizeof (hide int16_t_ctype);
  aligned_divides a max_align int16_t_alignof;
  int16_t_claim_uninit a;
  a
}

fn int16_t_stack_free (a: ptr)
  requires int16_t_pts_to_uninit a
{
  I.int16_t_stack_free a
}

fn int32_t_read (a: ptr) (#p: perm) (#x: erased I32.t)
  preserves int32_t_pts_to a p x
  returns  y : I32.t
  ensures  rewrites_to y (reveal x)
{
  int32_t_reveal a;
  with b e. assert (mem_pts_to_at a p b e);
  int32_t_repr_no_prov (reveal x) b;
  let y = I.int32_t_read_at a #p #x #(hide b) #e;
  int32_t_conceal a #p #b #(reveal x) #e;
  y
}

fn int32_t_write (a: ptr) (y: I32.t) (#x: erased I32.t)
  requires int32_t_pts_to a 1.0R x
  ensures  int32_t_pts_to a 1.0R y
{
  int32_t_reveal a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int32_t_sizeof) None (to_bits 32 (I32.v y));
  int32_t_repr_no_prov y b;
  EM.store a (hide int32_t_ctype) b;
  ET.store_read_ok e int32_t_ctype;
  int32_t_conceal a #1.0R #b #y #(EM.store_index e int32_t_ctype)
}

fn int32_t_write_uninit (a: ptr) (y: I32.t)
  requires int32_t_pts_to_uninit a
  ensures  int32_t_pts_to a 1.0R y
{
  int32_t_reveal_uninit a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int32_t_sizeof) None (to_bits 32 (I32.v y));
  int32_t_repr_no_prov y b;
  EM.store a (hide int32_t_ctype) b;
  ET.store_read_ok e int32_t_ctype;
  int32_t_conceal a #1.0R #b #y #(EM.store_index e int32_t_ctype)
}

fn int32_t_stack_alloc ()
  returns  a : ptr
  ensures  int32_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of int32_t_ctype true))
{
  let a = EM.stack_alloc int32_t_sizeof (hide int32_t_ctype);
  aligned_divides a max_align int32_t_alignof;
  int32_t_claim_uninit a;
  a
}

fn int32_t_stack_free (a: ptr)
  requires int32_t_pts_to_uninit a
{
  I.int32_t_stack_free a
}

fn int64_t_read (a: ptr) (#p: perm) (#x: erased I64.t)
  preserves int64_t_pts_to a p x
  returns  y : I64.t
  ensures  rewrites_to y (reveal x)
{
  int64_t_reveal a;
  with b e. assert (mem_pts_to_at a p b e);
  int64_t_repr_no_prov (reveal x) b;
  let y = I.int64_t_read_at a #p #x #(hide b) #e;
  int64_t_conceal a #p #b #(reveal x) #e;
  y
}

fn int64_t_write (a: ptr) (y: I64.t) (#x: erased I64.t)
  requires int64_t_pts_to a 1.0R x
  ensures  int64_t_pts_to a 1.0R y
{
  int64_t_reveal a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int64_t_sizeof) None (to_bits 64 (I64.v y));
  int64_t_repr_no_prov y b;
  EM.store a (hide int64_t_ctype) b;
  ET.store_read_ok e int64_t_ctype;
  int64_t_conceal a #1.0R #b #y #(EM.store_index e int64_t_ctype)
}

fn int64_t_write_uninit (a: ptr) (y: I64.t)
  requires int64_t_pts_to_uninit a
  ensures  int64_t_pts_to a 1.0R y
{
  int64_t_reveal_uninit a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int64_t_sizeof) None (to_bits 64 (I64.v y));
  int64_t_repr_no_prov y b;
  EM.store a (hide int64_t_ctype) b;
  ET.store_read_ok e int64_t_ctype;
  int64_t_conceal a #1.0R #b #y #(EM.store_index e int64_t_ctype)
}

fn int64_t_stack_alloc ()
  returns  a : ptr
  ensures  int64_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of int64_t_ctype true))
{
  let a = EM.stack_alloc int64_t_sizeof (hide int64_t_ctype);
  aligned_divides a max_align int64_t_alignof;
  int64_t_claim_uninit a;
  a
}

fn int64_t_stack_free (a: ptr)
  requires int64_t_pts_to_uninit a
{
  I.int64_t_stack_free a
}

fn uint8_t_write_uninit (a: ptr) (y: U8.t)
  requires uint8_t_pts_to_uninit a
  ensures  uint8_t_pts_to a 1.0R y
{
  uint8_t_reveal_uninit a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint8_t_sizeof) None (U8.v y);
  uint8_t_repr_no_prov y b;
  EM.store a (hide uint8_t_ctype) b;
  ET.store_read_ok e uint8_t_ctype;
  uint8_t_conceal a #1.0R #b #y #(EM.store_index e uint8_t_ctype)
}

fn uint8_t_stack_alloc ()
  returns  a : ptr
  ensures  uint8_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of uint8_t_ctype true))
{
  let a = EM.stack_alloc uint8_t_sizeof (hide uint8_t_ctype);
  aligned_divides a max_align uint8_t_alignof;
  uint8_t_claim_uninit a;
  a
}

fn uint8_t_stack_free (a: ptr)
  requires uint8_t_pts_to_uninit a
{
  I.uint8_t_stack_free a
}

fn uint16_t_read (a: ptr) (#p: perm) (#x: erased U16.t)
  preserves uint16_t_pts_to a p x
  returns  y : U16.t
  ensures  rewrites_to y (reveal x)
{
  uint16_t_reveal a;
  with b e. assert (mem_pts_to_at a p b e);
  uint16_t_repr_no_prov (reveal x) b;
  let y = I.uint16_t_read_at a #p #x #(hide b) #e;
  uint16_t_conceal a #p #b #(reveal x) #e;
  y
}

fn uint16_t_write (a: ptr) (y: U16.t) (#x: erased U16.t)
  requires uint16_t_pts_to a 1.0R x
  ensures  uint16_t_pts_to a 1.0R y
{
  uint16_t_reveal a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint16_t_sizeof) None (U16.v y);
  uint16_t_repr_no_prov y b;
  EM.store a (hide uint16_t_ctype) b;
  ET.store_read_ok e uint16_t_ctype;
  uint16_t_conceal a #1.0R #b #y #(EM.store_index e uint16_t_ctype)
}

fn uint16_t_write_uninit (a: ptr) (y: U16.t)
  requires uint16_t_pts_to_uninit a
  ensures  uint16_t_pts_to a 1.0R y
{
  uint16_t_reveal_uninit a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint16_t_sizeof) None (U16.v y);
  uint16_t_repr_no_prov y b;
  EM.store a (hide uint16_t_ctype) b;
  ET.store_read_ok e uint16_t_ctype;
  uint16_t_conceal a #1.0R #b #y #(EM.store_index e uint16_t_ctype)
}

fn uint16_t_stack_alloc ()
  returns  a : ptr
  ensures  uint16_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of uint16_t_ctype true))
{
  let a = EM.stack_alloc uint16_t_sizeof (hide uint16_t_ctype);
  aligned_divides a max_align uint16_t_alignof;
  uint16_t_claim_uninit a;
  a
}

fn uint16_t_stack_free (a: ptr)
  requires uint16_t_pts_to_uninit a
{
  I.uint16_t_stack_free a
}

fn uint64_t_read (a: ptr) (#p: perm) (#x: erased U64.t)
  preserves uint64_t_pts_to a p x
  returns  y : U64.t
  ensures  rewrites_to y (reveal x)
{
  uint64_t_reveal a;
  with b e. assert (mem_pts_to_at a p b e);
  uint64_t_repr_no_prov (reveal x) b;
  let y = I.uint64_t_read_at a #p #x #(hide b) #e;
  uint64_t_conceal a #p #b #(reveal x) #e;
  y
}

fn uint64_t_write (a: ptr) (y: U64.t) (#x: erased U64.t)
  requires uint64_t_pts_to a 1.0R x
  ensures  uint64_t_pts_to a 1.0R y
{
  uint64_t_reveal a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint64_t_sizeof) None (U64.v y);
  uint64_t_repr_no_prov y b;
  EM.store a (hide uint64_t_ctype) b;
  ET.store_read_ok e uint64_t_ctype;
  uint64_t_conceal a #1.0R #b #y #(EM.store_index e uint64_t_ctype)
}

fn uint64_t_write_uninit (a: ptr) (y: U64.t)
  requires uint64_t_pts_to_uninit a
  ensures  uint64_t_pts_to a 1.0R y
{
  uint64_t_reveal_uninit a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint64_t_sizeof) None (U64.v y);
  uint64_t_repr_no_prov y b;
  EM.store a (hide uint64_t_ctype) b;
  ET.store_read_ok e uint64_t_ctype;
  uint64_t_conceal a #1.0R #b #y #(EM.store_index e uint64_t_ctype)
}

fn uint64_t_stack_alloc ()
  returns  a : ptr
  ensures  uint64_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of uint64_t_ctype true))
{
  let a = EM.stack_alloc uint64_t_sizeof (hide uint64_t_ctype);
  aligned_divides a max_align uint64_t_alignof;
  uint64_t_claim_uninit a;
  a
}

fn uint64_t_stack_free (a: ptr)
  requires uint64_t_pts_to_uninit a
{
  I.uint64_t_stack_free a
}

fn size_t_read (a: ptr) (#p: perm) (#x: erased SZ.t)
  preserves size_t_pts_to a p x
  returns  y : SZ.t
  ensures  rewrites_to y (reveal x)
{
  size_t_reveal a;
  with b e. assert (mem_pts_to_at a p b e);
  size_t_repr_no_prov (reveal x) b;
  let y = I.size_t_read_at a #p #x #(hide b) #e;
  size_t_conceal a #p #b #(reveal x) #e;
  y
}

fn size_t_write (a: ptr) (y: SZ.t) (#x: erased SZ.t)
  requires size_t_pts_to a 1.0R x
  ensures  size_t_pts_to a 1.0R y
{
  size_t_reveal a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v size_t_sizeof) None (SZ.v y);
  size_t_repr_no_prov y b;
  EM.store a (hide size_t_ctype) b;
  ET.store_read_ok e size_t_ctype;
  size_t_conceal a #1.0R #b #y #(EM.store_index e size_t_ctype)
}

fn size_t_write_uninit (a: ptr) (y: SZ.t)
  requires size_t_pts_to_uninit a
  ensures  size_t_pts_to a 1.0R y
{
  size_t_reveal_uninit a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v size_t_sizeof) None (SZ.v y);
  size_t_repr_no_prov y b;
  EM.store a (hide size_t_ctype) b;
  ET.store_read_ok e size_t_ctype;
  size_t_conceal a #1.0R #b #y #(EM.store_index e size_t_ctype)
}

fn size_t_stack_alloc ()
  returns  a : ptr
  ensures  size_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of size_t_ctype true))
{
  let a = EM.stack_alloc size_t_sizeof (hide size_t_ctype);
  aligned_divides a max_align size_t_alignof;
  size_t_claim_uninit a;
  a
}

fn size_t_stack_free (a: ptr)
  requires size_t_pts_to_uninit a
{
  I.size_t_stack_free a
}

fn float32_t_read (a: ptr) (#p: perm) (#x: erased float32)
  preserves float32_t_pts_to a p x
  returns  y : float32
  ensures  rewrites_to y (reveal x)
{
  float32_t_reveal a;
  with b e. assert (mem_pts_to_at a p b e);
  float32_t_repr_no_prov (reveal x) b;
  let y = I.float32_t_read_at a #p #x #(hide b) #e;
  float32_t_conceal a #p #b #(reveal x) #e;
  y
}

fn float32_t_write (a: ptr) (y: float32) (#x: erased float32)
  requires float32_t_pts_to a 1.0R x
  ensures  float32_t_pts_to a 1.0R y
{
  float32_t_reveal a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v float32_t_sizeof) None (float32_bits y);
  float32_t_repr_no_prov y b;
  EM.store a (hide float32_t_ctype) b;
  ET.store_read_ok e float32_t_ctype;
  float32_t_conceal a #1.0R #b #y #(EM.store_index e float32_t_ctype)
}

fn float32_t_write_uninit (a: ptr) (y: float32)
  requires float32_t_pts_to_uninit a
  ensures  float32_t_pts_to a 1.0R y
{
  float32_t_reveal_uninit a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v float32_t_sizeof) None (float32_bits y);
  float32_t_repr_no_prov y b;
  EM.store a (hide float32_t_ctype) b;
  ET.store_read_ok e float32_t_ctype;
  float32_t_conceal a #1.0R #b #y #(EM.store_index e float32_t_ctype)
}

fn float32_t_stack_alloc ()
  returns  a : ptr
  ensures  float32_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of float32_t_ctype true))
{
  let a = EM.stack_alloc float32_t_sizeof (hide float32_t_ctype);
  aligned_divides a max_align float32_t_alignof;
  float32_t_claim_uninit a;
  a
}

fn float32_t_stack_free (a: ptr)
  requires float32_t_pts_to_uninit a
{
  I.float32_t_stack_free a
}

fn float64_t_read (a: ptr) (#p: perm) (#x: erased float64)
  preserves float64_t_pts_to a p x
  returns  y : float64
  ensures  rewrites_to y (reveal x)
{
  float64_t_reveal a;
  with b e. assert (mem_pts_to_at a p b e);
  float64_t_repr_no_prov (reveal x) b;
  let y = I.float64_t_read_at a #p #x #(hide b) #e;
  float64_t_conceal a #p #b #(reveal x) #e;
  y
}

fn float64_t_write (a: ptr) (y: float64) (#x: erased float64)
  requires float64_t_pts_to a 1.0R x
  ensures  float64_t_pts_to a 1.0R y
{
  float64_t_reveal a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v float64_t_sizeof) None (float64_bits y);
  float64_t_repr_no_prov y b;
  EM.store a (hide float64_t_ctype) b;
  ET.store_read_ok e float64_t_ctype;
  float64_t_conceal a #1.0R #b #y #(EM.store_index e float64_t_ctype)
}

fn float64_t_write_uninit (a: ptr) (y: float64)
  requires float64_t_pts_to_uninit a
  ensures  float64_t_pts_to a 1.0R y
{
  float64_t_reveal_uninit a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v float64_t_sizeof) None (float64_bits y);
  float64_t_repr_no_prov y b;
  EM.store a (hide float64_t_ctype) b;
  ET.store_read_ok e float64_t_ctype;
  float64_t_conceal a #1.0R #b #y #(EM.store_index e float64_t_ctype)
}

fn float64_t_stack_alloc ()
  returns  a : ptr
  ensures  float64_t_pts_to_uninit a
  ensures pure (fixed_metadata a (ET.etypes_of float64_t_ctype true))
{
  let a = EM.stack_alloc float64_t_sizeof (hide float64_t_ctype);
  aligned_divides a max_align float64_t_alignof;
  float64_t_claim_uninit a;
  a
}

fn float64_t_stack_free (a: ptr)
  requires float64_t_pts_to_uninit a
{
  I.float64_t_stack_free a
}

fn memcpy (dst src: ptr) (n: SZ.t)
          (#p: perm) (#bs #bd: erased bytes) (#ed: ET.etypes)
          (#es: ET.etypes { ET.copy_complete_ok (ET.Ready ed) (ET.Ready es) })
  preserves mem_pts_to_at src p bs es
  requires mem_pts_to_at dst 1.0R bd ed
  requires pure (len bs == SZ.v n /\ len bd == SZ.v n /\
                 ET.elen es == len bs /\ ET.elen ed == len bd /\
                 ET.copy_complete_ok (ET.Ready ed) (ET.Ready es))
  ensures mem_pts_to_at dst 1.0R bs
    (ET.state_etypes (ET.complete_copy (ET.Ready ed) (ET.Ready es)))
{
  EM.memcpy dst src n
}

fn memcpy_prefix (dst src: ptr) (n: SZ.t)
          (#p: perm) (#bs: erased bytes { SZ.v n <= len bs }) (#bd: erased bytes)
          (#ed: ET.etypes)
          (#es: ET.etypes { ET.elen es == len bs /\
                            ET.copy_complete_ok (ET.Ready ed) (ET.Ready (Seq.slice es 0 (SZ.v n))) })
  preserves mem_pts_to_at src p bs es
  requires mem_pts_to_at dst 1.0R bd ed
  requires pure (len bd == SZ.v n /\ ET.elen ed == len bd)
  ensures mem_pts_to_at dst 1.0R (slice bs 0 (SZ.v n))
    (ET.state_etypes (ET.complete_copy (ET.Ready ed) (ET.Ready (Seq.slice es 0 (SZ.v n)))))
{
  mem_split_at src n;
  memcpy dst src n;
  mem_join_at src n;
  slice_append bs (SZ.v n);
  Seq.lemma_split es (SZ.v n);
  Seq.lemma_eq_elim (Seq.append (Seq.slice es 0 (SZ.v n)) (Seq.slice es (SZ.v n) (ET.elen es))) es;
  rewrite each append (slice bs 0 (SZ.v n)) (slice bs (SZ.v n) (len bs)) as reveal bs,
               Seq.append (Seq.slice es 0 (SZ.v n)) (Seq.slice es (SZ.v n) (ET.elen es)) as es;
}

(* A byte copy between objects that have no effective type. *)
fn memcpy_untyped (dst src: ptr) (n: SZ.t)
          (#p: perm) (#bs #bd: erased bytes)
  preserves mem_pts_to_at src p bs (Seq.create (SZ.v n) None)
  requires mem_pts_to_at dst 1.0R bd (Seq.create (SZ.v n) None)
  requires pure (len bs == SZ.v n /\ len bd == SZ.v n)
  ensures mem_pts_to_at dst 1.0R bs (Seq.create (SZ.v n) None)
{
  EM.memcpy_untyped dst src n
}

fn memset_zero (dst: ptr) (n: SZ.t) (#bd: erased bytes) (#ed: ET.etypes)
  requires mem_pts_to_at dst 1.0R bd ed
  requires pure (len bd == SZ.v n /\ ET.elen ed == len bd)
  ensures mem_pts_to_at dst 1.0R (zeroed (SZ.v n)) ed
{
  EM.memset_zero dst n
}

fn mem_stack_alloc (n: SZ.t) (ct: erased ET.ctype)
  requires pure (SZ.v n == ET.csize (reveal ct))
  returns a: ptr
  ensures mem_pts_to_at a 1.0R (uninit (SZ.v n)) (ET.etypes_of (reveal ct) true)
    ** pure (aligned a max_align /\ fixed_metadata a (ET.etypes_of (reveal ct) true))
{
  EM.stack_alloc n ct
}

fn mem_stack_free (a: ptr) (#b: erased bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
{
  I.mem_stack_free a
}

fn uint32_t_read_at (a: ptr) (#p: perm) (#x: erased U32.t) (#e: ET.etypes)
  preserves V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a p x e
  returns y: U32.t
  ensures rewrites_to y (reveal x)
{
  V.reveal_value uint32_t_ctype uint32_t_repr uint32_t_alignof a;
  with b. assert (mem_pts_to_at a p b e);
  uint32_t_repr_no_prov (reveal x) b;
  let y = I.uint32_t_read_at a #p #x #(hide b) #e;
  V.claim uint32_t_ctype uint32_t_repr uint32_t_alignof a #p #(reveal x) #b #e;
  y
}

fn uint32_t_write_at (a: ptr) (y: U32.t) (#x: erased U32.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint32_t_ctype })
  requires V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a 1.0R x e
  ensures V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a 1.0R y (EM.store_index e uint32_t_ctype)
{
  V.reveal_value uint32_t_ctype uint32_t_repr uint32_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint32_t_sizeof) None (U32.v y);
  uint32_t_repr_no_prov y b;
  EM.store a (hide uint32_t_ctype) b;
  ET.store_read_ok e uint32_t_ctype;
  V.claim uint32_t_ctype uint32_t_repr uint32_t_alignof a #1.0R #y #b #(EM.store_index e uint32_t_ctype)
}

fn uint32_t_write_uninit_at (a: ptr) (y: U32.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint32_t_ctype })
  requires V.storage uint32_t_ctype uint32_t_alignof a e
  ensures V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a 1.0R y (EM.store_index e uint32_t_ctype)
{
  V.reveal_storage uint32_t_ctype uint32_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint32_t_sizeof) None (U32.v y);
  uint32_t_repr_no_prov y b;
  EM.store a (hide uint32_t_ctype) b;
  ET.store_read_ok e uint32_t_ctype;
  V.claim uint32_t_ctype uint32_t_repr uint32_t_alignof a #1.0R #y #b #(EM.store_index e uint32_t_ctype)
}

fn uint32_t_write_existing (a: ptr) (y: U32.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint32_t_ctype })
  requires V.storage uint32_t_ctype uint32_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a 1.0R y e
{
  V.reveal_storage uint32_t_ctype uint32_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  ET.store_readable_stable e uint32_t_ctype;
  V.claim_storage uint32_t_ctype uint32_t_alignof a;
  uint32_t_write_uninit_at a y;
}

fn uint32_t_initialize_at (a: ptr) (y: U32.t)
  requires E.prepared a uint32_t_ctype
  requires pure (aligned a uint32_t_alignof)
  ensures exists* e. V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type uint32_t_ctype) ==> e == ET.etypes_of uint32_t_ctype false))
{
  let b = Enc.encode (SZ.v uint32_t_sizeof) None (U32.v y);
  uint32_t_repr_no_prov y b;
  EM.initialize a (hide uint32_t_ctype) b;
  with e. assert (mem_pts_to_at a 1.0R b e);
  V.claim uint32_t_ctype uint32_t_repr uint32_t_alignof a #1.0R #y #b #e;
}

fn uint32_t_initialize (a: ptr) (y: U32.t)
  requires E.prepared a uint32_t_ctype
  requires pure (aligned a uint32_t_alignof)
  ensures uint32_t_pts_to a 1.0R y
{
  uint32_t_initialize_at a y;
  with e. assert (V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a 1.0R y e);
  V.reveal_value uint32_t_ctype uint32_t_repr uint32_t_alignof a;
  with b. assert (mem_pts_to_at a 1.0R b e);
  uint32_t_conceal a #1.0R #b #y #e;
}

fn uint8_t_read_at (a: ptr) (#p: perm) (#x: erased U8.t) (#e: ET.etypes)
  preserves V.value uint8_t_ctype uint8_t_repr uint8_t_alignof a p x e
  returns y: U8.t
  ensures rewrites_to y (reveal x)
{
  V.reveal_value uint8_t_ctype uint8_t_repr uint8_t_alignof a;
  with b. assert (mem_pts_to_at a p b e);
  uint8_t_repr_no_prov (reveal x) b;
  let y = I.uint8_t_read_at a #p #x #(hide b) #e;
  V.claim uint8_t_ctype uint8_t_repr uint8_t_alignof a #p #(reveal x) #b #e;
  y
}

fn uint8_t_write_at (a: ptr) (y: U8.t) (#x: erased U8.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint8_t_ctype })
  requires V.value uint8_t_ctype uint8_t_repr uint8_t_alignof a 1.0R x e
  ensures V.value uint8_t_ctype uint8_t_repr uint8_t_alignof a 1.0R y (EM.store_index e uint8_t_ctype)
{
  V.reveal_value uint8_t_ctype uint8_t_repr uint8_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint8_t_sizeof) None (U8.v y);
  uint8_t_repr_no_prov y b;
  EM.store a (hide uint8_t_ctype) b;
  ET.store_read_ok e uint8_t_ctype;
  V.claim uint8_t_ctype uint8_t_repr uint8_t_alignof a #1.0R #y #b #(EM.store_index e uint8_t_ctype)
}

fn uint8_t_write_uninit_at (a: ptr) (y: U8.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint8_t_ctype })
  requires V.storage uint8_t_ctype uint8_t_alignof a e
  ensures V.value uint8_t_ctype uint8_t_repr uint8_t_alignof a 1.0R y (EM.store_index e uint8_t_ctype)
{
  V.reveal_storage uint8_t_ctype uint8_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint8_t_sizeof) None (U8.v y);
  uint8_t_repr_no_prov y b;
  EM.store a (hide uint8_t_ctype) b;
  ET.store_read_ok e uint8_t_ctype;
  V.claim uint8_t_ctype uint8_t_repr uint8_t_alignof a #1.0R #y #b #(EM.store_index e uint8_t_ctype)
}

fn uint8_t_write_existing (a: ptr) (y: U8.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint8_t_ctype })
  requires V.storage uint8_t_ctype uint8_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value uint8_t_ctype uint8_t_repr uint8_t_alignof a 1.0R y e
{
  V.reveal_storage uint8_t_ctype uint8_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  ET.store_readable_stable e uint8_t_ctype;
  V.claim_storage uint8_t_ctype uint8_t_alignof a;
  uint8_t_write_uninit_at a y;
}

fn uint8_t_initialize_at (a: ptr) (y: U8.t)
  requires E.prepared a uint8_t_ctype
  requires pure (aligned a uint8_t_alignof)
  ensures exists* e. V.value uint8_t_ctype uint8_t_repr uint8_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type uint8_t_ctype) ==> e == ET.etypes_of uint8_t_ctype false))
{
  let b = Enc.encode (SZ.v uint8_t_sizeof) None (U8.v y);
  uint8_t_repr_no_prov y b;
  EM.initialize a (hide uint8_t_ctype) b;
  with e. assert (mem_pts_to_at a 1.0R b e);
  V.claim uint8_t_ctype uint8_t_repr uint8_t_alignof a #1.0R #y #b #e;
}

fn uint8_t_initialize (a: ptr) (y: U8.t)
  requires E.prepared a uint8_t_ctype
  requires pure (aligned a uint8_t_alignof)
  ensures uint8_t_pts_to a 1.0R y
{
  uint8_t_initialize_at a y;
  with e. assert (V.value uint8_t_ctype uint8_t_repr uint8_t_alignof a 1.0R y e);
  V.reveal_value uint8_t_ctype uint8_t_repr uint8_t_alignof a;
  with b. assert (mem_pts_to_at a 1.0R b e);
  uint8_t_conceal a #1.0R #b #y #e;
}

fn ptr_read_at (a: ptr) (#p: perm) (#x: erased ptr) (#e: ET.etypes)
  preserves V.value ptr_ctype ptr_repr ptr_alignof a p x e
  returns y: ptr
  ensures rewrites_to y (reveal x)
{
  V.reveal_value ptr_ctype ptr_repr ptr_alignof a;
  with b. assert (mem_pts_to_at a p b e);
  ptr_repr_len (reveal x) b;
  let y = I.ptr_read_at a #p #x #(hide b) #e;
  V.claim ptr_ctype ptr_repr ptr_alignof a #p #(reveal x) #b #e;
  y
}

fn ptr_write_at (a: ptr) (y: ptr) (#x: erased ptr)
    (#e: ET.etypes { ET.elen e == ET.csize ptr_ctype })
  requires V.value ptr_ctype ptr_repr ptr_alignof a 1.0R x e
  ensures V.value ptr_ctype ptr_repr ptr_alignof a 1.0R y (EM.store_index e ptr_ctype)
{
  V.reveal_value ptr_ctype ptr_repr ptr_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  I.ptr_store a y;
  ET.store_read_ok e ptr_ctype;
  V.claim ptr_ctype ptr_repr ptr_alignof a #1.0R #y #(Enc.encode (SZ.v ptr_sizeof) (prov_of y) (addr_of y)) #(EM.store_index e ptr_ctype)
}

fn ptr_write_uninit_at (a: ptr) (y: ptr)
    (#e: ET.etypes { ET.elen e == ET.csize ptr_ctype })
  requires V.storage ptr_ctype ptr_alignof a e
  ensures V.value ptr_ctype ptr_repr ptr_alignof a 1.0R y (EM.store_index e ptr_ctype)
{
  V.reveal_storage ptr_ctype ptr_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  I.ptr_store a y;
  ET.store_read_ok e ptr_ctype;
  V.claim ptr_ctype ptr_repr ptr_alignof a #1.0R #y #(Enc.encode (SZ.v ptr_sizeof) (prov_of y) (addr_of y)) #(EM.store_index e ptr_ctype)
}

fn ptr_write_existing (a: ptr) (y: ptr)
    (#e: ET.etypes { ET.elen e == ET.csize ptr_ctype })
  requires V.storage ptr_ctype ptr_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value ptr_ctype ptr_repr ptr_alignof a 1.0R y e
{
  V.reveal_storage ptr_ctype ptr_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  ET.store_readable_stable e ptr_ctype;
  V.claim_storage ptr_ctype ptr_alignof a;
  ptr_write_uninit_at a y;
}

fn ptr_initialize_at (a: ptr) (y: ptr)
  requires E.prepared a ptr_ctype
  requires pure (aligned a ptr_alignof)
  ensures exists* e. V.value ptr_ctype ptr_repr ptr_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type ptr_ctype) ==> e == ET.etypes_of ptr_ctype false))
{
  I.ptr_initialize a y;
  ET.read_ok_of ptr_ctype false;
  V.claim ptr_ctype ptr_repr ptr_alignof a #1.0R #y
    #(Enc.encode (SZ.v ptr_sizeof) (prov_of y) (addr_of y))
    #(ET.etypes_of ptr_ctype false);
}

fn ptr_initialize (a: ptr) (y: ptr)
  requires E.prepared a ptr_ctype
  requires pure (aligned a ptr_alignof)
  ensures ptr_pts_to a 1.0R y
{
  ptr_initialize_at a y;
  with e. assert (V.value ptr_ctype ptr_repr ptr_alignof a 1.0R y e);
  V.reveal_value ptr_ctype ptr_repr ptr_alignof a;
  with b. assert (mem_pts_to_at a 1.0R b e);
  ptr_conceal a #1.0R #b #y #e;
}

fn bool_t_read_at (a: ptr) (#p: perm) (#x: erased bool) (#e: ET.etypes)
  preserves V.value bool_t_ctype bool_t_repr bool_t_alignof a p x e
  returns y: bool
  ensures rewrites_to y (reveal x)
{
  V.reveal_value bool_t_ctype bool_t_repr bool_t_alignof a;
  with b. assert (mem_pts_to_at a p b e);
  bool_t_repr_no_prov (reveal x) b;
  let y = I.bool_t_read_at a #p #x #(hide b) #e;
  V.claim bool_t_ctype bool_t_repr bool_t_alignof a #p #(reveal x) #b #e;
  y
}

fn bool_t_write_at (a: ptr) (y: bool) (#x: erased bool)
    (#e: ET.etypes { ET.elen e == ET.csize bool_t_ctype })
  requires V.value bool_t_ctype bool_t_repr bool_t_alignof a 1.0R x e
  ensures V.value bool_t_ctype bool_t_repr bool_t_alignof a 1.0R y (EM.store_index e bool_t_ctype)
{
  V.reveal_value bool_t_ctype bool_t_repr bool_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v bool_t_sizeof) None (if y then 1 else 0);
  bool_t_repr_no_prov y b;
  EM.store a (hide bool_t_ctype) b;
  ET.store_read_ok e bool_t_ctype;
  V.claim bool_t_ctype bool_t_repr bool_t_alignof a #1.0R #y #b #(EM.store_index e bool_t_ctype)
}

fn bool_t_write_uninit_at (a: ptr) (y: bool)
    (#e: ET.etypes { ET.elen e == ET.csize bool_t_ctype })
  requires V.storage bool_t_ctype bool_t_alignof a e
  ensures V.value bool_t_ctype bool_t_repr bool_t_alignof a 1.0R y (EM.store_index e bool_t_ctype)
{
  V.reveal_storage bool_t_ctype bool_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v bool_t_sizeof) None (if y then 1 else 0);
  bool_t_repr_no_prov y b;
  EM.store a (hide bool_t_ctype) b;
  ET.store_read_ok e bool_t_ctype;
  V.claim bool_t_ctype bool_t_repr bool_t_alignof a #1.0R #y #b #(EM.store_index e bool_t_ctype)
}

fn bool_t_write_existing (a: ptr) (y: bool)
    (#e: ET.etypes { ET.elen e == ET.csize bool_t_ctype })
  requires V.storage bool_t_ctype bool_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value bool_t_ctype bool_t_repr bool_t_alignof a 1.0R y e
{
  V.reveal_storage bool_t_ctype bool_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  ET.store_readable_stable e bool_t_ctype;
  V.claim_storage bool_t_ctype bool_t_alignof a;
  bool_t_write_uninit_at a y;
}

fn bool_t_initialize_at (a: ptr) (y: bool)
  requires E.prepared a bool_t_ctype
  requires pure (aligned a bool_t_alignof)
  ensures exists* e. V.value bool_t_ctype bool_t_repr bool_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type bool_t_ctype) ==> e == ET.etypes_of bool_t_ctype false))
{
  let b = Enc.encode (SZ.v bool_t_sizeof) None (if y then 1 else 0);
  bool_t_repr_no_prov y b;
  EM.initialize a (hide bool_t_ctype) b;
  with e. assert (mem_pts_to_at a 1.0R b e);
  V.claim bool_t_ctype bool_t_repr bool_t_alignof a #1.0R #y #b #e;
}

fn bool_t_initialize (a: ptr) (y: bool)
  requires E.prepared a bool_t_ctype
  requires pure (aligned a bool_t_alignof)
  ensures bool_t_pts_to a 1.0R y
{
  bool_t_initialize_at a y;
  with e. assert (V.value bool_t_ctype bool_t_repr bool_t_alignof a 1.0R y e);
  V.reveal_value bool_t_ctype bool_t_repr bool_t_alignof a;
  with b. assert (mem_pts_to_at a 1.0R b e);
  bool_t_conceal a #1.0R #b #y #e;
}

fn int8_t_read_at (a: ptr) (#p: perm) (#x: erased I8.t) (#e: ET.etypes)
  preserves V.value int8_t_ctype int8_t_repr int8_t_alignof a p x e
  returns y: I8.t
  ensures rewrites_to y (reveal x)
{
  V.reveal_value int8_t_ctype int8_t_repr int8_t_alignof a;
  with b. assert (mem_pts_to_at a p b e);
  int8_t_repr_no_prov (reveal x) b;
  let y = I.int8_t_read_at a #p #x #(hide b) #e;
  V.claim int8_t_ctype int8_t_repr int8_t_alignof a #p #(reveal x) #b #e;
  y
}

fn int8_t_write_at (a: ptr) (y: I8.t) (#x: erased I8.t)
    (#e: ET.etypes { ET.elen e == ET.csize int8_t_ctype })
  requires V.value int8_t_ctype int8_t_repr int8_t_alignof a 1.0R x e
  ensures V.value int8_t_ctype int8_t_repr int8_t_alignof a 1.0R y (EM.store_index e int8_t_ctype)
{
  V.reveal_value int8_t_ctype int8_t_repr int8_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int8_t_sizeof) None (to_bits 8 (I8.v y));
  int8_t_repr_no_prov y b;
  EM.store a (hide int8_t_ctype) b;
  ET.store_read_ok e int8_t_ctype;
  V.claim int8_t_ctype int8_t_repr int8_t_alignof a #1.0R #y #b #(EM.store_index e int8_t_ctype)
}

fn int8_t_write_uninit_at (a: ptr) (y: I8.t)
    (#e: ET.etypes { ET.elen e == ET.csize int8_t_ctype })
  requires V.storage int8_t_ctype int8_t_alignof a e
  ensures V.value int8_t_ctype int8_t_repr int8_t_alignof a 1.0R y (EM.store_index e int8_t_ctype)
{
  V.reveal_storage int8_t_ctype int8_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int8_t_sizeof) None (to_bits 8 (I8.v y));
  int8_t_repr_no_prov y b;
  EM.store a (hide int8_t_ctype) b;
  ET.store_read_ok e int8_t_ctype;
  V.claim int8_t_ctype int8_t_repr int8_t_alignof a #1.0R #y #b #(EM.store_index e int8_t_ctype)
}

fn int8_t_write_existing (a: ptr) (y: I8.t)
    (#e: ET.etypes { ET.elen e == ET.csize int8_t_ctype })
  requires V.storage int8_t_ctype int8_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value int8_t_ctype int8_t_repr int8_t_alignof a 1.0R y e
{
  V.reveal_storage int8_t_ctype int8_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  ET.store_readable_stable e int8_t_ctype;
  V.claim_storage int8_t_ctype int8_t_alignof a;
  int8_t_write_uninit_at a y;
}

fn int8_t_initialize_at (a: ptr) (y: I8.t)
  requires E.prepared a int8_t_ctype
  requires pure (aligned a int8_t_alignof)
  ensures exists* e. V.value int8_t_ctype int8_t_repr int8_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type int8_t_ctype) ==> e == ET.etypes_of int8_t_ctype false))
{
  let b = Enc.encode (SZ.v int8_t_sizeof) None (to_bits 8 (I8.v y));
  int8_t_repr_no_prov y b;
  EM.initialize a (hide int8_t_ctype) b;
  with e. assert (mem_pts_to_at a 1.0R b e);
  V.claim int8_t_ctype int8_t_repr int8_t_alignof a #1.0R #y #b #e;
}

fn int8_t_initialize (a: ptr) (y: I8.t)
  requires E.prepared a int8_t_ctype
  requires pure (aligned a int8_t_alignof)
  ensures int8_t_pts_to a 1.0R y
{
  int8_t_initialize_at a y;
  with e. assert (V.value int8_t_ctype int8_t_repr int8_t_alignof a 1.0R y e);
  V.reveal_value int8_t_ctype int8_t_repr int8_t_alignof a;
  with b. assert (mem_pts_to_at a 1.0R b e);
  int8_t_conceal a #1.0R #b #y #e;
}

fn int16_t_read_at (a: ptr) (#p: perm) (#x: erased I16.t) (#e: ET.etypes)
  preserves V.value int16_t_ctype int16_t_repr int16_t_alignof a p x e
  returns y: I16.t
  ensures rewrites_to y (reveal x)
{
  V.reveal_value int16_t_ctype int16_t_repr int16_t_alignof a;
  with b. assert (mem_pts_to_at a p b e);
  int16_t_repr_no_prov (reveal x) b;
  let y = I.int16_t_read_at a #p #x #(hide b) #e;
  V.claim int16_t_ctype int16_t_repr int16_t_alignof a #p #(reveal x) #b #e;
  y
}

fn int16_t_write_at (a: ptr) (y: I16.t) (#x: erased I16.t)
    (#e: ET.etypes { ET.elen e == ET.csize int16_t_ctype })
  requires V.value int16_t_ctype int16_t_repr int16_t_alignof a 1.0R x e
  ensures V.value int16_t_ctype int16_t_repr int16_t_alignof a 1.0R y (EM.store_index e int16_t_ctype)
{
  V.reveal_value int16_t_ctype int16_t_repr int16_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int16_t_sizeof) None (to_bits 16 (I16.v y));
  int16_t_repr_no_prov y b;
  EM.store a (hide int16_t_ctype) b;
  ET.store_read_ok e int16_t_ctype;
  V.claim int16_t_ctype int16_t_repr int16_t_alignof a #1.0R #y #b #(EM.store_index e int16_t_ctype)
}

fn int16_t_write_uninit_at (a: ptr) (y: I16.t)
    (#e: ET.etypes { ET.elen e == ET.csize int16_t_ctype })
  requires V.storage int16_t_ctype int16_t_alignof a e
  ensures V.value int16_t_ctype int16_t_repr int16_t_alignof a 1.0R y (EM.store_index e int16_t_ctype)
{
  V.reveal_storage int16_t_ctype int16_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int16_t_sizeof) None (to_bits 16 (I16.v y));
  int16_t_repr_no_prov y b;
  EM.store a (hide int16_t_ctype) b;
  ET.store_read_ok e int16_t_ctype;
  V.claim int16_t_ctype int16_t_repr int16_t_alignof a #1.0R #y #b #(EM.store_index e int16_t_ctype)
}

fn int16_t_write_existing (a: ptr) (y: I16.t)
    (#e: ET.etypes { ET.elen e == ET.csize int16_t_ctype })
  requires V.storage int16_t_ctype int16_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value int16_t_ctype int16_t_repr int16_t_alignof a 1.0R y e
{
  V.reveal_storage int16_t_ctype int16_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  ET.store_readable_stable e int16_t_ctype;
  V.claim_storage int16_t_ctype int16_t_alignof a;
  int16_t_write_uninit_at a y;
}

fn int16_t_initialize_at (a: ptr) (y: I16.t)
  requires E.prepared a int16_t_ctype
  requires pure (aligned a int16_t_alignof)
  ensures exists* e. V.value int16_t_ctype int16_t_repr int16_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type int16_t_ctype) ==> e == ET.etypes_of int16_t_ctype false))
{
  let b = Enc.encode (SZ.v int16_t_sizeof) None (to_bits 16 (I16.v y));
  int16_t_repr_no_prov y b;
  EM.initialize a (hide int16_t_ctype) b;
  with e. assert (mem_pts_to_at a 1.0R b e);
  V.claim int16_t_ctype int16_t_repr int16_t_alignof a #1.0R #y #b #e;
}

fn int16_t_initialize (a: ptr) (y: I16.t)
  requires E.prepared a int16_t_ctype
  requires pure (aligned a int16_t_alignof)
  ensures int16_t_pts_to a 1.0R y
{
  int16_t_initialize_at a y;
  with e. assert (V.value int16_t_ctype int16_t_repr int16_t_alignof a 1.0R y e);
  V.reveal_value int16_t_ctype int16_t_repr int16_t_alignof a;
  with b. assert (mem_pts_to_at a 1.0R b e);
  int16_t_conceal a #1.0R #b #y #e;
}

fn int32_t_read_at (a: ptr) (#p: perm) (#x: erased I32.t) (#e: ET.etypes)
  preserves V.value int32_t_ctype int32_t_repr int32_t_alignof a p x e
  returns y: I32.t
  ensures rewrites_to y (reveal x)
{
  V.reveal_value int32_t_ctype int32_t_repr int32_t_alignof a;
  with b. assert (mem_pts_to_at a p b e);
  int32_t_repr_no_prov (reveal x) b;
  let y = I.int32_t_read_at a #p #x #(hide b) #e;
  V.claim int32_t_ctype int32_t_repr int32_t_alignof a #p #(reveal x) #b #e;
  y
}

fn int32_t_write_at (a: ptr) (y: I32.t) (#x: erased I32.t)
    (#e: ET.etypes { ET.elen e == ET.csize int32_t_ctype })
  requires V.value int32_t_ctype int32_t_repr int32_t_alignof a 1.0R x e
  ensures V.value int32_t_ctype int32_t_repr int32_t_alignof a 1.0R y (EM.store_index e int32_t_ctype)
{
  V.reveal_value int32_t_ctype int32_t_repr int32_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int32_t_sizeof) None (to_bits 32 (I32.v y));
  int32_t_repr_no_prov y b;
  EM.store a (hide int32_t_ctype) b;
  ET.store_read_ok e int32_t_ctype;
  V.claim int32_t_ctype int32_t_repr int32_t_alignof a #1.0R #y #b #(EM.store_index e int32_t_ctype)
}

fn int32_t_write_uninit_at (a: ptr) (y: I32.t)
    (#e: ET.etypes { ET.elen e == ET.csize int32_t_ctype })
  requires V.storage int32_t_ctype int32_t_alignof a e
  ensures V.value int32_t_ctype int32_t_repr int32_t_alignof a 1.0R y (EM.store_index e int32_t_ctype)
{
  V.reveal_storage int32_t_ctype int32_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int32_t_sizeof) None (to_bits 32 (I32.v y));
  int32_t_repr_no_prov y b;
  EM.store a (hide int32_t_ctype) b;
  ET.store_read_ok e int32_t_ctype;
  V.claim int32_t_ctype int32_t_repr int32_t_alignof a #1.0R #y #b #(EM.store_index e int32_t_ctype)
}

fn int32_t_write_existing (a: ptr) (y: I32.t)
    (#e: ET.etypes { ET.elen e == ET.csize int32_t_ctype })
  requires V.storage int32_t_ctype int32_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value int32_t_ctype int32_t_repr int32_t_alignof a 1.0R y e
{
  V.reveal_storage int32_t_ctype int32_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  ET.store_readable_stable e int32_t_ctype;
  V.claim_storage int32_t_ctype int32_t_alignof a;
  int32_t_write_uninit_at a y;
}

fn int32_t_initialize_at (a: ptr) (y: I32.t)
  requires E.prepared a int32_t_ctype
  requires pure (aligned a int32_t_alignof)
  ensures exists* e. V.value int32_t_ctype int32_t_repr int32_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type int32_t_ctype) ==> e == ET.etypes_of int32_t_ctype false))
{
  let b = Enc.encode (SZ.v int32_t_sizeof) None (to_bits 32 (I32.v y));
  int32_t_repr_no_prov y b;
  EM.initialize a (hide int32_t_ctype) b;
  with e. assert (mem_pts_to_at a 1.0R b e);
  V.claim int32_t_ctype int32_t_repr int32_t_alignof a #1.0R #y #b #e;
}

fn int32_t_initialize (a: ptr) (y: I32.t)
  requires E.prepared a int32_t_ctype
  requires pure (aligned a int32_t_alignof)
  ensures int32_t_pts_to a 1.0R y
{
  int32_t_initialize_at a y;
  with e. assert (V.value int32_t_ctype int32_t_repr int32_t_alignof a 1.0R y e);
  V.reveal_value int32_t_ctype int32_t_repr int32_t_alignof a;
  with b. assert (mem_pts_to_at a 1.0R b e);
  int32_t_conceal a #1.0R #b #y #e;
}

fn int64_t_read_at (a: ptr) (#p: perm) (#x: erased I64.t) (#e: ET.etypes)
  preserves V.value int64_t_ctype int64_t_repr int64_t_alignof a p x e
  returns y: I64.t
  ensures rewrites_to y (reveal x)
{
  V.reveal_value int64_t_ctype int64_t_repr int64_t_alignof a;
  with b. assert (mem_pts_to_at a p b e);
  int64_t_repr_no_prov (reveal x) b;
  let y = I.int64_t_read_at a #p #x #(hide b) #e;
  V.claim int64_t_ctype int64_t_repr int64_t_alignof a #p #(reveal x) #b #e;
  y
}

fn int64_t_write_at (a: ptr) (y: I64.t) (#x: erased I64.t)
    (#e: ET.etypes { ET.elen e == ET.csize int64_t_ctype })
  requires V.value int64_t_ctype int64_t_repr int64_t_alignof a 1.0R x e
  ensures V.value int64_t_ctype int64_t_repr int64_t_alignof a 1.0R y (EM.store_index e int64_t_ctype)
{
  V.reveal_value int64_t_ctype int64_t_repr int64_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int64_t_sizeof) None (to_bits 64 (I64.v y));
  int64_t_repr_no_prov y b;
  EM.store a (hide int64_t_ctype) b;
  ET.store_read_ok e int64_t_ctype;
  V.claim int64_t_ctype int64_t_repr int64_t_alignof a #1.0R #y #b #(EM.store_index e int64_t_ctype)
}

fn int64_t_write_uninit_at (a: ptr) (y: I64.t)
    (#e: ET.etypes { ET.elen e == ET.csize int64_t_ctype })
  requires V.storage int64_t_ctype int64_t_alignof a e
  ensures V.value int64_t_ctype int64_t_repr int64_t_alignof a 1.0R y (EM.store_index e int64_t_ctype)
{
  V.reveal_storage int64_t_ctype int64_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int64_t_sizeof) None (to_bits 64 (I64.v y));
  int64_t_repr_no_prov y b;
  EM.store a (hide int64_t_ctype) b;
  ET.store_read_ok e int64_t_ctype;
  V.claim int64_t_ctype int64_t_repr int64_t_alignof a #1.0R #y #b #(EM.store_index e int64_t_ctype)
}

fn int64_t_write_existing (a: ptr) (y: I64.t)
    (#e: ET.etypes { ET.elen e == ET.csize int64_t_ctype })
  requires V.storage int64_t_ctype int64_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value int64_t_ctype int64_t_repr int64_t_alignof a 1.0R y e
{
  V.reveal_storage int64_t_ctype int64_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  ET.store_readable_stable e int64_t_ctype;
  V.claim_storage int64_t_ctype int64_t_alignof a;
  int64_t_write_uninit_at a y;
}

fn int64_t_initialize_at (a: ptr) (y: I64.t)
  requires E.prepared a int64_t_ctype
  requires pure (aligned a int64_t_alignof)
  ensures exists* e. V.value int64_t_ctype int64_t_repr int64_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type int64_t_ctype) ==> e == ET.etypes_of int64_t_ctype false))
{
  let b = Enc.encode (SZ.v int64_t_sizeof) None (to_bits 64 (I64.v y));
  int64_t_repr_no_prov y b;
  EM.initialize a (hide int64_t_ctype) b;
  with e. assert (mem_pts_to_at a 1.0R b e);
  V.claim int64_t_ctype int64_t_repr int64_t_alignof a #1.0R #y #b #e;
}

fn int64_t_initialize (a: ptr) (y: I64.t)
  requires E.prepared a int64_t_ctype
  requires pure (aligned a int64_t_alignof)
  ensures int64_t_pts_to a 1.0R y
{
  int64_t_initialize_at a y;
  with e. assert (V.value int64_t_ctype int64_t_repr int64_t_alignof a 1.0R y e);
  V.reveal_value int64_t_ctype int64_t_repr int64_t_alignof a;
  with b. assert (mem_pts_to_at a 1.0R b e);
  int64_t_conceal a #1.0R #b #y #e;
}

fn uint16_t_read_at (a: ptr) (#p: perm) (#x: erased U16.t) (#e: ET.etypes)
  preserves V.value uint16_t_ctype uint16_t_repr uint16_t_alignof a p x e
  returns y: U16.t
  ensures rewrites_to y (reveal x)
{
  V.reveal_value uint16_t_ctype uint16_t_repr uint16_t_alignof a;
  with b. assert (mem_pts_to_at a p b e);
  uint16_t_repr_no_prov (reveal x) b;
  let y = I.uint16_t_read_at a #p #x #(hide b) #e;
  V.claim uint16_t_ctype uint16_t_repr uint16_t_alignof a #p #(reveal x) #b #e;
  y
}

fn uint16_t_write_at (a: ptr) (y: U16.t) (#x: erased U16.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint16_t_ctype })
  requires V.value uint16_t_ctype uint16_t_repr uint16_t_alignof a 1.0R x e
  ensures V.value uint16_t_ctype uint16_t_repr uint16_t_alignof a 1.0R y (EM.store_index e uint16_t_ctype)
{
  V.reveal_value uint16_t_ctype uint16_t_repr uint16_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint16_t_sizeof) None (U16.v y);
  uint16_t_repr_no_prov y b;
  EM.store a (hide uint16_t_ctype) b;
  ET.store_read_ok e uint16_t_ctype;
  V.claim uint16_t_ctype uint16_t_repr uint16_t_alignof a #1.0R #y #b #(EM.store_index e uint16_t_ctype)
}

fn uint16_t_write_uninit_at (a: ptr) (y: U16.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint16_t_ctype })
  requires V.storage uint16_t_ctype uint16_t_alignof a e
  ensures V.value uint16_t_ctype uint16_t_repr uint16_t_alignof a 1.0R y (EM.store_index e uint16_t_ctype)
{
  V.reveal_storage uint16_t_ctype uint16_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint16_t_sizeof) None (U16.v y);
  uint16_t_repr_no_prov y b;
  EM.store a (hide uint16_t_ctype) b;
  ET.store_read_ok e uint16_t_ctype;
  V.claim uint16_t_ctype uint16_t_repr uint16_t_alignof a #1.0R #y #b #(EM.store_index e uint16_t_ctype)
}

fn uint16_t_write_existing (a: ptr) (y: U16.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint16_t_ctype })
  requires V.storage uint16_t_ctype uint16_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value uint16_t_ctype uint16_t_repr uint16_t_alignof a 1.0R y e
{
  V.reveal_storage uint16_t_ctype uint16_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  ET.store_readable_stable e uint16_t_ctype;
  V.claim_storage uint16_t_ctype uint16_t_alignof a;
  uint16_t_write_uninit_at a y;
}

fn uint16_t_initialize_at (a: ptr) (y: U16.t)
  requires E.prepared a uint16_t_ctype
  requires pure (aligned a uint16_t_alignof)
  ensures exists* e. V.value uint16_t_ctype uint16_t_repr uint16_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type uint16_t_ctype) ==> e == ET.etypes_of uint16_t_ctype false))
{
  let b = Enc.encode (SZ.v uint16_t_sizeof) None (U16.v y);
  uint16_t_repr_no_prov y b;
  EM.initialize a (hide uint16_t_ctype) b;
  with e. assert (mem_pts_to_at a 1.0R b e);
  V.claim uint16_t_ctype uint16_t_repr uint16_t_alignof a #1.0R #y #b #e;
}

fn uint16_t_initialize (a: ptr) (y: U16.t)
  requires E.prepared a uint16_t_ctype
  requires pure (aligned a uint16_t_alignof)
  ensures uint16_t_pts_to a 1.0R y
{
  uint16_t_initialize_at a y;
  with e. assert (V.value uint16_t_ctype uint16_t_repr uint16_t_alignof a 1.0R y e);
  V.reveal_value uint16_t_ctype uint16_t_repr uint16_t_alignof a;
  with b. assert (mem_pts_to_at a 1.0R b e);
  uint16_t_conceal a #1.0R #b #y #e;
}

fn uint64_t_read_at (a: ptr) (#p: perm) (#x: erased U64.t) (#e: ET.etypes)
  preserves V.value uint64_t_ctype uint64_t_repr uint64_t_alignof a p x e
  returns y: U64.t
  ensures rewrites_to y (reveal x)
{
  V.reveal_value uint64_t_ctype uint64_t_repr uint64_t_alignof a;
  with b. assert (mem_pts_to_at a p b e);
  uint64_t_repr_no_prov (reveal x) b;
  let y = I.uint64_t_read_at a #p #x #(hide b) #e;
  V.claim uint64_t_ctype uint64_t_repr uint64_t_alignof a #p #(reveal x) #b #e;
  y
}

fn uint64_t_write_at (a: ptr) (y: U64.t) (#x: erased U64.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint64_t_ctype })
  requires V.value uint64_t_ctype uint64_t_repr uint64_t_alignof a 1.0R x e
  ensures V.value uint64_t_ctype uint64_t_repr uint64_t_alignof a 1.0R y (EM.store_index e uint64_t_ctype)
{
  V.reveal_value uint64_t_ctype uint64_t_repr uint64_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint64_t_sizeof) None (U64.v y);
  uint64_t_repr_no_prov y b;
  EM.store a (hide uint64_t_ctype) b;
  ET.store_read_ok e uint64_t_ctype;
  V.claim uint64_t_ctype uint64_t_repr uint64_t_alignof a #1.0R #y #b #(EM.store_index e uint64_t_ctype)
}

fn uint64_t_write_uninit_at (a: ptr) (y: U64.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint64_t_ctype })
  requires V.storage uint64_t_ctype uint64_t_alignof a e
  ensures V.value uint64_t_ctype uint64_t_repr uint64_t_alignof a 1.0R y (EM.store_index e uint64_t_ctype)
{
  V.reveal_storage uint64_t_ctype uint64_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint64_t_sizeof) None (U64.v y);
  uint64_t_repr_no_prov y b;
  EM.store a (hide uint64_t_ctype) b;
  ET.store_read_ok e uint64_t_ctype;
  V.claim uint64_t_ctype uint64_t_repr uint64_t_alignof a #1.0R #y #b #(EM.store_index e uint64_t_ctype)
}

fn uint64_t_write_existing (a: ptr) (y: U64.t)
    (#e: ET.etypes { ET.elen e == ET.csize uint64_t_ctype })
  requires V.storage uint64_t_ctype uint64_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value uint64_t_ctype uint64_t_repr uint64_t_alignof a 1.0R y e
{
  V.reveal_storage uint64_t_ctype uint64_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  ET.store_readable_stable e uint64_t_ctype;
  V.claim_storage uint64_t_ctype uint64_t_alignof a;
  uint64_t_write_uninit_at a y;
}

fn uint64_t_initialize_at (a: ptr) (y: U64.t)
  requires E.prepared a uint64_t_ctype
  requires pure (aligned a uint64_t_alignof)
  ensures exists* e. V.value uint64_t_ctype uint64_t_repr uint64_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type uint64_t_ctype) ==> e == ET.etypes_of uint64_t_ctype false))
{
  let b = Enc.encode (SZ.v uint64_t_sizeof) None (U64.v y);
  uint64_t_repr_no_prov y b;
  EM.initialize a (hide uint64_t_ctype) b;
  with e. assert (mem_pts_to_at a 1.0R b e);
  V.claim uint64_t_ctype uint64_t_repr uint64_t_alignof a #1.0R #y #b #e;
}

fn uint64_t_initialize (a: ptr) (y: U64.t)
  requires E.prepared a uint64_t_ctype
  requires pure (aligned a uint64_t_alignof)
  ensures uint64_t_pts_to a 1.0R y
{
  uint64_t_initialize_at a y;
  with e. assert (V.value uint64_t_ctype uint64_t_repr uint64_t_alignof a 1.0R y e);
  V.reveal_value uint64_t_ctype uint64_t_repr uint64_t_alignof a;
  with b. assert (mem_pts_to_at a 1.0R b e);
  uint64_t_conceal a #1.0R #b #y #e;
}

fn size_t_read_at (a: ptr) (#p: perm) (#x: erased SZ.t) (#e: ET.etypes)
  preserves V.value size_t_ctype size_t_repr size_t_alignof a p x e
  returns y: SZ.t
  ensures rewrites_to y (reveal x)
{
  V.reveal_value size_t_ctype size_t_repr size_t_alignof a;
  with b. assert (mem_pts_to_at a p b e);
  size_t_repr_no_prov (reveal x) b;
  let y = I.size_t_read_at a #p #x #(hide b) #e;
  V.claim size_t_ctype size_t_repr size_t_alignof a #p #(reveal x) #b #e;
  y
}

fn size_t_write_at (a: ptr) (y: SZ.t) (#x: erased SZ.t)
    (#e: ET.etypes { ET.elen e == ET.csize size_t_ctype })
  requires V.value size_t_ctype size_t_repr size_t_alignof a 1.0R x e
  ensures V.value size_t_ctype size_t_repr size_t_alignof a 1.0R y (EM.store_index e size_t_ctype)
{
  V.reveal_value size_t_ctype size_t_repr size_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v size_t_sizeof) None (SZ.v y);
  size_t_repr_no_prov y b;
  EM.store a (hide size_t_ctype) b;
  ET.store_read_ok e size_t_ctype;
  V.claim size_t_ctype size_t_repr size_t_alignof a #1.0R #y #b #(EM.store_index e size_t_ctype)
}

fn size_t_write_uninit_at (a: ptr) (y: SZ.t)
    (#e: ET.etypes { ET.elen e == ET.csize size_t_ctype })
  requires V.storage size_t_ctype size_t_alignof a e
  ensures V.value size_t_ctype size_t_repr size_t_alignof a 1.0R y (EM.store_index e size_t_ctype)
{
  V.reveal_storage size_t_ctype size_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v size_t_sizeof) None (SZ.v y);
  size_t_repr_no_prov y b;
  EM.store a (hide size_t_ctype) b;
  ET.store_read_ok e size_t_ctype;
  V.claim size_t_ctype size_t_repr size_t_alignof a #1.0R #y #b #(EM.store_index e size_t_ctype)
}

fn size_t_write_existing (a: ptr) (y: SZ.t)
    (#e: ET.etypes { ET.elen e == ET.csize size_t_ctype })
  requires V.storage size_t_ctype size_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value size_t_ctype size_t_repr size_t_alignof a 1.0R y e
{
  V.reveal_storage size_t_ctype size_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  ET.store_readable_stable e size_t_ctype;
  V.claim_storage size_t_ctype size_t_alignof a;
  size_t_write_uninit_at a y;
}

fn size_t_initialize_at (a: ptr) (y: SZ.t)
  requires E.prepared a size_t_ctype
  requires pure (aligned a size_t_alignof)
  ensures exists* e. V.value size_t_ctype size_t_repr size_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type size_t_ctype) ==> e == ET.etypes_of size_t_ctype false))
{
  let b = Enc.encode (SZ.v size_t_sizeof) None (SZ.v y);
  size_t_repr_no_prov y b;
  EM.initialize a (hide size_t_ctype) b;
  with e. assert (mem_pts_to_at a 1.0R b e);
  V.claim size_t_ctype size_t_repr size_t_alignof a #1.0R #y #b #e;
}

fn size_t_initialize (a: ptr) (y: SZ.t)
  requires E.prepared a size_t_ctype
  requires pure (aligned a size_t_alignof)
  ensures size_t_pts_to a 1.0R y
{
  size_t_initialize_at a y;
  with e. assert (V.value size_t_ctype size_t_repr size_t_alignof a 1.0R y e);
  V.reveal_value size_t_ctype size_t_repr size_t_alignof a;
  with b. assert (mem_pts_to_at a 1.0R b e);
  size_t_conceal a #1.0R #b #y #e;
}

fn float32_t_read_at (a: ptr) (#p: perm) (#x: erased float32) (#e: ET.etypes)
  preserves V.value float32_t_ctype float32_t_repr float32_t_alignof a p x e
  returns y: float32
  ensures rewrites_to y (reveal x)
{
  V.reveal_value float32_t_ctype float32_t_repr float32_t_alignof a;
  with b. assert (mem_pts_to_at a p b e);
  float32_t_repr_no_prov (reveal x) b;
  let y = I.float32_t_read_at a #p #x #(hide b) #e;
  V.claim float32_t_ctype float32_t_repr float32_t_alignof a #p #(reveal x) #b #e;
  y
}

fn float32_t_write_at (a: ptr) (y: float32) (#x: erased float32)
    (#e: ET.etypes { ET.elen e == ET.csize float32_t_ctype })
  requires V.value float32_t_ctype float32_t_repr float32_t_alignof a 1.0R x e
  ensures V.value float32_t_ctype float32_t_repr float32_t_alignof a 1.0R y (EM.store_index e float32_t_ctype)
{
  V.reveal_value float32_t_ctype float32_t_repr float32_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v float32_t_sizeof) None (float32_bits y);
  float32_t_repr_no_prov y b;
  EM.store a (hide float32_t_ctype) b;
  ET.store_read_ok e float32_t_ctype;
  V.claim float32_t_ctype float32_t_repr float32_t_alignof a #1.0R #y #b #(EM.store_index e float32_t_ctype)
}

fn float32_t_write_uninit_at (a: ptr) (y: float32)
    (#e: ET.etypes { ET.elen e == ET.csize float32_t_ctype })
  requires V.storage float32_t_ctype float32_t_alignof a e
  ensures V.value float32_t_ctype float32_t_repr float32_t_alignof a 1.0R y (EM.store_index e float32_t_ctype)
{
  V.reveal_storage float32_t_ctype float32_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v float32_t_sizeof) None (float32_bits y);
  float32_t_repr_no_prov y b;
  EM.store a (hide float32_t_ctype) b;
  ET.store_read_ok e float32_t_ctype;
  V.claim float32_t_ctype float32_t_repr float32_t_alignof a #1.0R #y #b #(EM.store_index e float32_t_ctype)
}

fn float32_t_write_existing (a: ptr) (y: float32)
    (#e: ET.etypes { ET.elen e == ET.csize float32_t_ctype })
  requires V.storage float32_t_ctype float32_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value float32_t_ctype float32_t_repr float32_t_alignof a 1.0R y e
{
  V.reveal_storage float32_t_ctype float32_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  ET.store_readable_stable e float32_t_ctype;
  V.claim_storage float32_t_ctype float32_t_alignof a;
  float32_t_write_uninit_at a y;
}

fn float32_t_initialize_at (a: ptr) (y: float32)
  requires E.prepared a float32_t_ctype
  requires pure (aligned a float32_t_alignof)
  ensures exists* e. V.value float32_t_ctype float32_t_repr float32_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type float32_t_ctype) ==> e == ET.etypes_of float32_t_ctype false))
{
  let b = Enc.encode (SZ.v float32_t_sizeof) None (float32_bits y);
  float32_t_repr_no_prov y b;
  EM.initialize a (hide float32_t_ctype) b;
  with e. assert (mem_pts_to_at a 1.0R b e);
  V.claim float32_t_ctype float32_t_repr float32_t_alignof a #1.0R #y #b #e;
}

fn float32_t_initialize (a: ptr) (y: float32)
  requires E.prepared a float32_t_ctype
  requires pure (aligned a float32_t_alignof)
  ensures float32_t_pts_to a 1.0R y
{
  float32_t_initialize_at a y;
  with e. assert (V.value float32_t_ctype float32_t_repr float32_t_alignof a 1.0R y e);
  V.reveal_value float32_t_ctype float32_t_repr float32_t_alignof a;
  with b. assert (mem_pts_to_at a 1.0R b e);
  float32_t_conceal a #1.0R #b #y #e;
}

fn float64_t_read_at (a: ptr) (#p: perm) (#x: erased float64) (#e: ET.etypes)
  preserves V.value float64_t_ctype float64_t_repr float64_t_alignof a p x e
  returns y: float64
  ensures rewrites_to y (reveal x)
{
  V.reveal_value float64_t_ctype float64_t_repr float64_t_alignof a;
  with b. assert (mem_pts_to_at a p b e);
  float64_t_repr_no_prov (reveal x) b;
  let y = I.float64_t_read_at a #p #x #(hide b) #e;
  V.claim float64_t_ctype float64_t_repr float64_t_alignof a #p #(reveal x) #b #e;
  y
}

fn float64_t_write_at (a: ptr) (y: float64) (#x: erased float64)
    (#e: ET.etypes { ET.elen e == ET.csize float64_t_ctype })
  requires V.value float64_t_ctype float64_t_repr float64_t_alignof a 1.0R x e
  ensures V.value float64_t_ctype float64_t_repr float64_t_alignof a 1.0R y (EM.store_index e float64_t_ctype)
{
  V.reveal_value float64_t_ctype float64_t_repr float64_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v float64_t_sizeof) None (float64_bits y);
  float64_t_repr_no_prov y b;
  EM.store a (hide float64_t_ctype) b;
  ET.store_read_ok e float64_t_ctype;
  V.claim float64_t_ctype float64_t_repr float64_t_alignof a #1.0R #y #b #(EM.store_index e float64_t_ctype)
}

fn float64_t_write_uninit_at (a: ptr) (y: float64)
    (#e: ET.etypes { ET.elen e == ET.csize float64_t_ctype })
  requires V.storage float64_t_ctype float64_t_alignof a e
  ensures V.value float64_t_ctype float64_t_repr float64_t_alignof a 1.0R y (EM.store_index e float64_t_ctype)
{
  V.reveal_storage float64_t_ctype float64_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v float64_t_sizeof) None (float64_bits y);
  float64_t_repr_no_prov y b;
  EM.store a (hide float64_t_ctype) b;
  ET.store_read_ok e float64_t_ctype;
  V.claim float64_t_ctype float64_t_repr float64_t_alignof a #1.0R #y #b #(EM.store_index e float64_t_ctype)
}

fn float64_t_write_existing (a: ptr) (y: float64)
    (#e: ET.etypes { ET.elen e == ET.csize float64_t_ctype })
  requires V.storage float64_t_ctype float64_t_alignof a e
  requires pure (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k))
  ensures V.value float64_t_ctype float64_t_repr float64_t_alignof a 1.0R y e
{
  V.reveal_storage float64_t_ctype float64_t_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  ET.store_readable_stable e float64_t_ctype;
  V.claim_storage float64_t_ctype float64_t_alignof a;
  float64_t_write_uninit_at a y;
}

fn float64_t_initialize_at (a: ptr) (y: float64)
  requires E.prepared a float64_t_ctype
  requires pure (aligned a float64_t_alignof)
  ensures exists* e. V.value float64_t_ctype float64_t_repr float64_t_alignof a 1.0R y e
    ** pure (E.mutable_index e /\
      (not (ET.character_type float64_t_ctype) ==> e == ET.etypes_of float64_t_ctype false))
{
  let b = Enc.encode (SZ.v float64_t_sizeof) None (float64_bits y);
  float64_t_repr_no_prov y b;
  EM.initialize a (hide float64_t_ctype) b;
  with e. assert (mem_pts_to_at a 1.0R b e);
  V.claim float64_t_ctype float64_t_repr float64_t_alignof a #1.0R #y #b #e;
}

fn float64_t_initialize (a: ptr) (y: float64)
  requires E.prepared a float64_t_ctype
  requires pure (aligned a float64_t_alignof)
  ensures float64_t_pts_to a 1.0R y
{
  float64_t_initialize_at a y;
  with e. assert (V.value float64_t_ctype float64_t_repr float64_t_alignof a 1.0R y e);
  V.reveal_value float64_t_ctype float64_t_repr float64_t_alignof a;
  with b. assert (mem_pts_to_at a 1.0R b e);
  float64_t_conceal a #1.0R #b #y #e;
}
