module Pulse.Lib.C.Palow.Unaligned

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Array
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.Float
open Pulse.Lib.C.Palow.CTypes
open Pulse.Lib.C.Palow.Machine
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64

module ET = Pulse.Lib.C.Palow.Etype
module EM = Pulse.Lib.C.Palow.Effective.Machine
module I = Pulse.Lib.C.Palow.Machine.Intrinsics
module Enc = Pulse.Lib.C.Palow.Encoding
open Pulse.Lib.C.Palow.Encoding

(* Unaligned typed operations obey the same metadata checks as aligned ones.
   They do not use source-level memcpy's effective-type transition to model
   an implementation detail of a load or store. *)
let bytes_uninit (ct: ET.ctype) ([@@@mkey] a: ptr) (n: nat) : slprop =
  exists* b e. mem_pts_to_at a 1.0R b e
    ** pure (len b == n /\ n == ET.csize ct /\ ET.elen e == len b /\ ET.read_ok e ct)

ghost fn bytes_claim_uninit (ct: ET.ctype) (a: ptr) (n: nat)
                             (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == n /\ n == ET.csize ct /\ ET.elen e == len b /\ ET.read_ok e ct)
  ensures bytes_uninit ct a n
{
  fold bytes_uninit ct a n;
}

ghost fn bytes_reveal_uninit (ct: ET.ctype) (a: ptr) (n: nat)
  requires bytes_uninit ct a n
  ensures exists* b e. mem_pts_to_at a 1.0R b e
    ** pure (len b == n /\ n == ET.csize ct /\ ET.elen e == len b /\ ET.read_ok e ct)
{
  unfold bytes_uninit ct a n;
}

ghost fn bool_t_forget_u (a: ptr) (#x: bool)
  requires elem_pts_to bool_t_ctype bool_t_repr a 1.0R x
  ensures  bytes_uninit bool_t_ctype a (SZ.v bool_t_sizeof)
{
  unfold elem_pts_to bool_t_ctype bool_t_repr a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  bool_t_repr_len x b;
  fold bytes_uninit bool_t_ctype a (SZ.v bool_t_sizeof);
}

fn bool_t_read_u (a: ptr) (#p: perm) (#x: erased bool)
  preserves elem_pts_to bool_t_ctype bool_t_repr a p x
  returns  y : bool
  ensures  rewrites_to y (reveal x)
{
  elem_reveal bool_t_ctype bool_t_repr a;
  with b e. assert (mem_pts_to_at a p b e);
  bool_t_repr_no_prov (reveal x) b;
  let y = I.bool_t_read_at a #p #x #(hide b) #e;
  elem_conceal bool_t_ctype bool_t_repr a #p #b #(reveal x) #e;
  y
}

fn bool_t_write_uninit_u (a: ptr) (y: bool)
  requires bytes_uninit bool_t_ctype a (SZ.v bool_t_sizeof)
  ensures  elem_pts_to bool_t_ctype bool_t_repr a 1.0R y
{
  unfold bytes_uninit bool_t_ctype a (SZ.v bool_t_sizeof);
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v bool_t_sizeof) None (if y then 1 else 0);
  bool_t_repr_no_prov y b;
  EM.store a (hide bool_t_ctype) b;
  ET.store_read_ok e bool_t_ctype;
  elem_conceal bool_t_ctype bool_t_repr a #1.0R #b #y #(EM.store_index e bool_t_ctype)
}

fn bool_t_write_u (a: ptr) (y: bool) (#x: erased bool)
  requires elem_pts_to bool_t_ctype bool_t_repr a 1.0R x
  ensures  elem_pts_to bool_t_ctype bool_t_repr a 1.0R y
{
  bool_t_forget_u a;
  bool_t_write_uninit_u a y
}

ghost fn int8_t_forget_u (a: ptr) (#x: I8.t)
  requires elem_pts_to int8_t_ctype int8_t_repr a 1.0R x
  ensures  bytes_uninit int8_t_ctype a (SZ.v int8_t_sizeof)
{
  unfold elem_pts_to int8_t_ctype int8_t_repr a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  int8_t_repr_len x b;
  fold bytes_uninit int8_t_ctype a (SZ.v int8_t_sizeof);
}

fn int8_t_read_u (a: ptr) (#p: perm) (#x: erased I8.t)
  preserves elem_pts_to int8_t_ctype int8_t_repr a p x
  returns  y : I8.t
  ensures  rewrites_to y (reveal x)
{
  elem_reveal int8_t_ctype int8_t_repr a;
  with b e. assert (mem_pts_to_at a p b e);
  int8_t_repr_no_prov (reveal x) b;
  let y = I.int8_t_read_at a #p #x #(hide b) #e;
  elem_conceal int8_t_ctype int8_t_repr a #p #b #(reveal x) #e;
  y
}

fn int8_t_write_uninit_u (a: ptr) (y: I8.t)
  requires bytes_uninit int8_t_ctype a (SZ.v int8_t_sizeof)
  ensures  elem_pts_to int8_t_ctype int8_t_repr a 1.0R y
{
  unfold bytes_uninit int8_t_ctype a (SZ.v int8_t_sizeof);
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int8_t_sizeof) None (to_bits 8 (I8.v y));
  int8_t_repr_no_prov y b;
  EM.store a (hide int8_t_ctype) b;
  ET.store_read_ok e int8_t_ctype;
  elem_conceal int8_t_ctype int8_t_repr a #1.0R #b #y #(EM.store_index e int8_t_ctype)
}

fn int8_t_write_u (a: ptr) (y: I8.t) (#x: erased I8.t)
  requires elem_pts_to int8_t_ctype int8_t_repr a 1.0R x
  ensures  elem_pts_to int8_t_ctype int8_t_repr a 1.0R y
{
  int8_t_forget_u a;
  int8_t_write_uninit_u a y
}

ghost fn uint8_t_forget_u (a: ptr) (#x: U8.t)
  requires elem_pts_to uint8_t_ctype uint8_t_repr a 1.0R x
  ensures  bytes_uninit uint8_t_ctype a (SZ.v uint8_t_sizeof)
{
  unfold elem_pts_to uint8_t_ctype uint8_t_repr a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  uint8_t_repr_len x b;
  fold bytes_uninit uint8_t_ctype a (SZ.v uint8_t_sizeof);
}

fn uint8_t_read_u (a: ptr) (#p: perm) (#x: erased U8.t)
  preserves elem_pts_to uint8_t_ctype uint8_t_repr a p x
  returns  y : U8.t
  ensures  rewrites_to y (reveal x)
{
  elem_reveal uint8_t_ctype uint8_t_repr a;
  with b e. assert (mem_pts_to_at a p b e);
  uint8_t_repr_no_prov (reveal x) b;
  let y = I.uint8_t_read_at a #p #x #(hide b) #e;
  elem_conceal uint8_t_ctype uint8_t_repr a #p #b #(reveal x) #e;
  y
}

fn uint8_t_write_uninit_u (a: ptr) (y: U8.t)
  requires bytes_uninit uint8_t_ctype a (SZ.v uint8_t_sizeof)
  ensures  elem_pts_to uint8_t_ctype uint8_t_repr a 1.0R y
{
  unfold bytes_uninit uint8_t_ctype a (SZ.v uint8_t_sizeof);
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint8_t_sizeof) None (U8.v y);
  uint8_t_repr_no_prov y b;
  EM.store a (hide uint8_t_ctype) b;
  ET.store_read_ok e uint8_t_ctype;
  elem_conceal uint8_t_ctype uint8_t_repr a #1.0R #b #y #(EM.store_index e uint8_t_ctype)
}

fn uint8_t_write_u (a: ptr) (y: U8.t) (#x: erased U8.t)
  requires elem_pts_to uint8_t_ctype uint8_t_repr a 1.0R x
  ensures  elem_pts_to uint8_t_ctype uint8_t_repr a 1.0R y
{
  uint8_t_forget_u a;
  uint8_t_write_uninit_u a y
}

ghost fn int16_t_forget_u (a: ptr) (#x: I16.t)
  requires elem_pts_to int16_t_ctype int16_t_repr a 1.0R x
  ensures  bytes_uninit int16_t_ctype a (SZ.v int16_t_sizeof)
{
  unfold elem_pts_to int16_t_ctype int16_t_repr a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  int16_t_repr_len x b;
  fold bytes_uninit int16_t_ctype a (SZ.v int16_t_sizeof);
}

fn int16_t_read_u (a: ptr) (#p: perm) (#x: erased I16.t)
  preserves elem_pts_to int16_t_ctype int16_t_repr a p x
  returns  y : I16.t
  ensures  rewrites_to y (reveal x)
{
  elem_reveal int16_t_ctype int16_t_repr a;
  with b e. assert (mem_pts_to_at a p b e);
  int16_t_repr_no_prov (reveal x) b;
  let y = I.int16_t_read_at a #p #x #(hide b) #e;
  elem_conceal int16_t_ctype int16_t_repr a #p #b #(reveal x) #e;
  y
}

fn int16_t_write_uninit_u (a: ptr) (y: I16.t)
  requires bytes_uninit int16_t_ctype a (SZ.v int16_t_sizeof)
  ensures  elem_pts_to int16_t_ctype int16_t_repr a 1.0R y
{
  unfold bytes_uninit int16_t_ctype a (SZ.v int16_t_sizeof);
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int16_t_sizeof) None (to_bits 16 (I16.v y));
  int16_t_repr_no_prov y b;
  EM.store a (hide int16_t_ctype) b;
  ET.store_read_ok e int16_t_ctype;
  elem_conceal int16_t_ctype int16_t_repr a #1.0R #b #y #(EM.store_index e int16_t_ctype)
}

fn int16_t_write_u (a: ptr) (y: I16.t) (#x: erased I16.t)
  requires elem_pts_to int16_t_ctype int16_t_repr a 1.0R x
  ensures  elem_pts_to int16_t_ctype int16_t_repr a 1.0R y
{
  int16_t_forget_u a;
  int16_t_write_uninit_u a y
}

ghost fn uint16_t_forget_u (a: ptr) (#x: U16.t)
  requires elem_pts_to uint16_t_ctype uint16_t_repr a 1.0R x
  ensures  bytes_uninit uint16_t_ctype a (SZ.v uint16_t_sizeof)
{
  unfold elem_pts_to uint16_t_ctype uint16_t_repr a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  uint16_t_repr_len x b;
  fold bytes_uninit uint16_t_ctype a (SZ.v uint16_t_sizeof);
}

fn uint16_t_read_u (a: ptr) (#p: perm) (#x: erased U16.t)
  preserves elem_pts_to uint16_t_ctype uint16_t_repr a p x
  returns  y : U16.t
  ensures  rewrites_to y (reveal x)
{
  elem_reveal uint16_t_ctype uint16_t_repr a;
  with b e. assert (mem_pts_to_at a p b e);
  uint16_t_repr_no_prov (reveal x) b;
  let y = I.uint16_t_read_at a #p #x #(hide b) #e;
  elem_conceal uint16_t_ctype uint16_t_repr a #p #b #(reveal x) #e;
  y
}

fn uint16_t_write_uninit_u (a: ptr) (y: U16.t)
  requires bytes_uninit uint16_t_ctype a (SZ.v uint16_t_sizeof)
  ensures  elem_pts_to uint16_t_ctype uint16_t_repr a 1.0R y
{
  unfold bytes_uninit uint16_t_ctype a (SZ.v uint16_t_sizeof);
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint16_t_sizeof) None (U16.v y);
  uint16_t_repr_no_prov y b;
  EM.store a (hide uint16_t_ctype) b;
  ET.store_read_ok e uint16_t_ctype;
  elem_conceal uint16_t_ctype uint16_t_repr a #1.0R #b #y #(EM.store_index e uint16_t_ctype)
}

fn uint16_t_write_u (a: ptr) (y: U16.t) (#x: erased U16.t)
  requires elem_pts_to uint16_t_ctype uint16_t_repr a 1.0R x
  ensures  elem_pts_to uint16_t_ctype uint16_t_repr a 1.0R y
{
  uint16_t_forget_u a;
  uint16_t_write_uninit_u a y
}

ghost fn int32_t_forget_u (a: ptr) (#x: I32.t)
  requires elem_pts_to int32_t_ctype int32_t_repr a 1.0R x
  ensures  bytes_uninit int32_t_ctype a (SZ.v int32_t_sizeof)
{
  unfold elem_pts_to int32_t_ctype int32_t_repr a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  int32_t_repr_len x b;
  fold bytes_uninit int32_t_ctype a (SZ.v int32_t_sizeof);
}

fn int32_t_read_u (a: ptr) (#p: perm) (#x: erased I32.t)
  preserves elem_pts_to int32_t_ctype int32_t_repr a p x
  returns  y : I32.t
  ensures  rewrites_to y (reveal x)
{
  elem_reveal int32_t_ctype int32_t_repr a;
  with b e. assert (mem_pts_to_at a p b e);
  int32_t_repr_no_prov (reveal x) b;
  let y = I.int32_t_read_at a #p #x #(hide b) #e;
  elem_conceal int32_t_ctype int32_t_repr a #p #b #(reveal x) #e;
  y
}

fn int32_t_write_uninit_u (a: ptr) (y: I32.t)
  requires bytes_uninit int32_t_ctype a (SZ.v int32_t_sizeof)
  ensures  elem_pts_to int32_t_ctype int32_t_repr a 1.0R y
{
  unfold bytes_uninit int32_t_ctype a (SZ.v int32_t_sizeof);
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int32_t_sizeof) None (to_bits 32 (I32.v y));
  int32_t_repr_no_prov y b;
  EM.store a (hide int32_t_ctype) b;
  ET.store_read_ok e int32_t_ctype;
  elem_conceal int32_t_ctype int32_t_repr a #1.0R #b #y #(EM.store_index e int32_t_ctype)
}

fn int32_t_write_u (a: ptr) (y: I32.t) (#x: erased I32.t)
  requires elem_pts_to int32_t_ctype int32_t_repr a 1.0R x
  ensures  elem_pts_to int32_t_ctype int32_t_repr a 1.0R y
{
  int32_t_forget_u a;
  int32_t_write_uninit_u a y
}

ghost fn uint32_t_forget_u (a: ptr) (#x: U32.t)
  requires elem_pts_to uint32_t_ctype uint32_t_repr a 1.0R x
  ensures  bytes_uninit uint32_t_ctype a (SZ.v uint32_t_sizeof)
{
  unfold elem_pts_to uint32_t_ctype uint32_t_repr a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  uint32_t_repr_len x b;
  fold bytes_uninit uint32_t_ctype a (SZ.v uint32_t_sizeof);
}

fn uint32_t_read_u (a: ptr) (#p: perm) (#x: erased U32.t)
  preserves elem_pts_to uint32_t_ctype uint32_t_repr a p x
  returns  y : U32.t
  ensures  rewrites_to y (reveal x)
{
  elem_reveal uint32_t_ctype uint32_t_repr a;
  with b e. assert (mem_pts_to_at a p b e);
  uint32_t_repr_no_prov (reveal x) b;
  let y = I.uint32_t_read_at a #p #x #(hide b) #e;
  elem_conceal uint32_t_ctype uint32_t_repr a #p #b #(reveal x) #e;
  y
}

fn uint32_t_write_uninit_u (a: ptr) (y: U32.t)
  requires bytes_uninit uint32_t_ctype a (SZ.v uint32_t_sizeof)
  ensures  elem_pts_to uint32_t_ctype uint32_t_repr a 1.0R y
{
  unfold bytes_uninit uint32_t_ctype a (SZ.v uint32_t_sizeof);
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint32_t_sizeof) None (U32.v y);
  uint32_t_repr_no_prov y b;
  EM.store a (hide uint32_t_ctype) b;
  ET.store_read_ok e uint32_t_ctype;
  elem_conceal uint32_t_ctype uint32_t_repr a #1.0R #b #y #(EM.store_index e uint32_t_ctype)
}

fn uint32_t_write_u (a: ptr) (y: U32.t) (#x: erased U32.t)
  requires elem_pts_to uint32_t_ctype uint32_t_repr a 1.0R x
  ensures  elem_pts_to uint32_t_ctype uint32_t_repr a 1.0R y
{
  uint32_t_forget_u a;
  uint32_t_write_uninit_u a y
}

ghost fn int64_t_forget_u (a: ptr) (#x: I64.t)
  requires elem_pts_to int64_t_ctype int64_t_repr a 1.0R x
  ensures  bytes_uninit int64_t_ctype a (SZ.v int64_t_sizeof)
{
  unfold elem_pts_to int64_t_ctype int64_t_repr a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  int64_t_repr_len x b;
  fold bytes_uninit int64_t_ctype a (SZ.v int64_t_sizeof);
}

fn int64_t_read_u (a: ptr) (#p: perm) (#x: erased I64.t)
  preserves elem_pts_to int64_t_ctype int64_t_repr a p x
  returns  y : I64.t
  ensures  rewrites_to y (reveal x)
{
  elem_reveal int64_t_ctype int64_t_repr a;
  with b e. assert (mem_pts_to_at a p b e);
  int64_t_repr_no_prov (reveal x) b;
  let y = I.int64_t_read_at a #p #x #(hide b) #e;
  elem_conceal int64_t_ctype int64_t_repr a #p #b #(reveal x) #e;
  y
}

fn int64_t_write_uninit_u (a: ptr) (y: I64.t)
  requires bytes_uninit int64_t_ctype a (SZ.v int64_t_sizeof)
  ensures  elem_pts_to int64_t_ctype int64_t_repr a 1.0R y
{
  unfold bytes_uninit int64_t_ctype a (SZ.v int64_t_sizeof);
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v int64_t_sizeof) None (to_bits 64 (I64.v y));
  int64_t_repr_no_prov y b;
  EM.store a (hide int64_t_ctype) b;
  ET.store_read_ok e int64_t_ctype;
  elem_conceal int64_t_ctype int64_t_repr a #1.0R #b #y #(EM.store_index e int64_t_ctype)
}

fn int64_t_write_u (a: ptr) (y: I64.t) (#x: erased I64.t)
  requires elem_pts_to int64_t_ctype int64_t_repr a 1.0R x
  ensures  elem_pts_to int64_t_ctype int64_t_repr a 1.0R y
{
  int64_t_forget_u a;
  int64_t_write_uninit_u a y
}

ghost fn uint64_t_forget_u (a: ptr) (#x: U64.t)
  requires elem_pts_to uint64_t_ctype uint64_t_repr a 1.0R x
  ensures  bytes_uninit uint64_t_ctype a (SZ.v uint64_t_sizeof)
{
  unfold elem_pts_to uint64_t_ctype uint64_t_repr a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  uint64_t_repr_len x b;
  fold bytes_uninit uint64_t_ctype a (SZ.v uint64_t_sizeof);
}

fn uint64_t_read_u (a: ptr) (#p: perm) (#x: erased U64.t)
  preserves elem_pts_to uint64_t_ctype uint64_t_repr a p x
  returns  y : U64.t
  ensures  rewrites_to y (reveal x)
{
  elem_reveal uint64_t_ctype uint64_t_repr a;
  with b e. assert (mem_pts_to_at a p b e);
  uint64_t_repr_no_prov (reveal x) b;
  let y = I.uint64_t_read_at a #p #x #(hide b) #e;
  elem_conceal uint64_t_ctype uint64_t_repr a #p #b #(reveal x) #e;
  y
}

fn uint64_t_write_uninit_u (a: ptr) (y: U64.t)
  requires bytes_uninit uint64_t_ctype a (SZ.v uint64_t_sizeof)
  ensures  elem_pts_to uint64_t_ctype uint64_t_repr a 1.0R y
{
  unfold bytes_uninit uint64_t_ctype a (SZ.v uint64_t_sizeof);
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v uint64_t_sizeof) None (U64.v y);
  uint64_t_repr_no_prov y b;
  EM.store a (hide uint64_t_ctype) b;
  ET.store_read_ok e uint64_t_ctype;
  elem_conceal uint64_t_ctype uint64_t_repr a #1.0R #b #y #(EM.store_index e uint64_t_ctype)
}

fn uint64_t_write_u (a: ptr) (y: U64.t) (#x: erased U64.t)
  requires elem_pts_to uint64_t_ctype uint64_t_repr a 1.0R x
  ensures  elem_pts_to uint64_t_ctype uint64_t_repr a 1.0R y
{
  uint64_t_forget_u a;
  uint64_t_write_uninit_u a y
}

(* long long / unsigned long long: the same representation as int64_t /
   uint64_t, but distinct effective types (6.2.5p4; 6.2.7p1). *)

ghost fn long_long_t_forget_u (a: ptr) (#x: I64.t)
  requires elem_pts_to long_long_t_ctype long_long_t_repr a 1.0R x
  ensures  bytes_uninit long_long_t_ctype a (SZ.v long_long_t_sizeof)
{
  unfold elem_pts_to long_long_t_ctype long_long_t_repr a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  long_long_t_repr_len x b;
  fold bytes_uninit long_long_t_ctype a (SZ.v long_long_t_sizeof);
}

fn long_long_t_read_u (a: ptr) (#p: perm) (#x: erased I64.t)
  preserves elem_pts_to long_long_t_ctype long_long_t_repr a p x
  returns  y : I64.t
  ensures  rewrites_to y (reveal x)
{
  elem_reveal long_long_t_ctype long_long_t_repr a;
  with b e. assert (mem_pts_to_at a p b e);
  long_long_t_repr_no_prov (reveal x) b;
  let y = I.long_long_t_read_at a #p #x #(hide b) #e;
  elem_conceal long_long_t_ctype long_long_t_repr a #p #b #(reveal x) #e;
  y
}

fn long_long_t_write_uninit_u (a: ptr) (y: I64.t)
  requires bytes_uninit long_long_t_ctype a (SZ.v long_long_t_sizeof)
  ensures  elem_pts_to long_long_t_ctype long_long_t_repr a 1.0R y
{
  unfold bytes_uninit long_long_t_ctype a (SZ.v long_long_t_sizeof);
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v long_long_t_sizeof) None (to_bits 64 (I64.v y));
  long_long_t_repr_no_prov y b;
  EM.store a (hide long_long_t_ctype) b;
  ET.store_read_ok e long_long_t_ctype;
  elem_conceal long_long_t_ctype long_long_t_repr a #1.0R #b #y #(EM.store_index e long_long_t_ctype)
}

fn long_long_t_write_u (a: ptr) (y: I64.t) (#x: erased I64.t)
  requires elem_pts_to long_long_t_ctype long_long_t_repr a 1.0R x
  ensures  elem_pts_to long_long_t_ctype long_long_t_repr a 1.0R y
{
  long_long_t_forget_u a;
  long_long_t_write_uninit_u a y
}

ghost fn ulong_long_t_forget_u (a: ptr) (#x: U64.t)
  requires elem_pts_to ulong_long_t_ctype ulong_long_t_repr a 1.0R x
  ensures  bytes_uninit ulong_long_t_ctype a (SZ.v ulong_long_t_sizeof)
{
  unfold elem_pts_to ulong_long_t_ctype ulong_long_t_repr a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  ulong_long_t_repr_len x b;
  fold bytes_uninit ulong_long_t_ctype a (SZ.v ulong_long_t_sizeof);
}

fn ulong_long_t_read_u (a: ptr) (#p: perm) (#x: erased U64.t)
  preserves elem_pts_to ulong_long_t_ctype ulong_long_t_repr a p x
  returns  y : U64.t
  ensures  rewrites_to y (reveal x)
{
  elem_reveal ulong_long_t_ctype ulong_long_t_repr a;
  with b e. assert (mem_pts_to_at a p b e);
  ulong_long_t_repr_no_prov (reveal x) b;
  let y = I.ulong_long_t_read_at a #p #x #(hide b) #e;
  elem_conceal ulong_long_t_ctype ulong_long_t_repr a #p #b #(reveal x) #e;
  y
}

fn ulong_long_t_write_uninit_u (a: ptr) (y: U64.t)
  requires bytes_uninit ulong_long_t_ctype a (SZ.v ulong_long_t_sizeof)
  ensures  elem_pts_to ulong_long_t_ctype ulong_long_t_repr a 1.0R y
{
  unfold bytes_uninit ulong_long_t_ctype a (SZ.v ulong_long_t_sizeof);
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v ulong_long_t_sizeof) None (U64.v y);
  ulong_long_t_repr_no_prov y b;
  EM.store a (hide ulong_long_t_ctype) b;
  ET.store_read_ok e ulong_long_t_ctype;
  elem_conceal ulong_long_t_ctype ulong_long_t_repr a #1.0R #b #y #(EM.store_index e ulong_long_t_ctype)
}

fn ulong_long_t_write_u (a: ptr) (y: U64.t) (#x: erased U64.t)
  requires elem_pts_to ulong_long_t_ctype ulong_long_t_repr a 1.0R x
  ensures  elem_pts_to ulong_long_t_ctype ulong_long_t_repr a 1.0R y
{
  ulong_long_t_forget_u a;
  ulong_long_t_write_uninit_u a y
}

ghost fn size_t_forget_u (a: ptr) (#x: SZ.t)
  requires elem_pts_to size_t_ctype size_t_repr a 1.0R x
  ensures  bytes_uninit size_t_ctype a (SZ.v size_t_sizeof)
{
  unfold elem_pts_to size_t_ctype size_t_repr a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  size_t_repr_len x b;
  fold bytes_uninit size_t_ctype a (SZ.v size_t_sizeof);
}

fn size_t_read_u (a: ptr) (#p: perm) (#x: erased SZ.t)
  preserves elem_pts_to size_t_ctype size_t_repr a p x
  returns  y : SZ.t
  ensures  rewrites_to y (reveal x)
{
  elem_reveal size_t_ctype size_t_repr a;
  with b e. assert (mem_pts_to_at a p b e);
  size_t_repr_no_prov (reveal x) b;
  let y = I.size_t_read_at a #p #x #(hide b) #e;
  elem_conceal size_t_ctype size_t_repr a #p #b #(reveal x) #e;
  y
}

fn size_t_write_uninit_u (a: ptr) (y: SZ.t)
  requires bytes_uninit size_t_ctype a (SZ.v size_t_sizeof)
  ensures  elem_pts_to size_t_ctype size_t_repr a 1.0R y
{
  unfold bytes_uninit size_t_ctype a (SZ.v size_t_sizeof);
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v size_t_sizeof) None (SZ.v y);
  size_t_repr_no_prov y b;
  EM.store a (hide size_t_ctype) b;
  ET.store_read_ok e size_t_ctype;
  elem_conceal size_t_ctype size_t_repr a #1.0R #b #y #(EM.store_index e size_t_ctype)
}

fn size_t_write_u (a: ptr) (y: SZ.t) (#x: erased SZ.t)
  requires elem_pts_to size_t_ctype size_t_repr a 1.0R x
  ensures  elem_pts_to size_t_ctype size_t_repr a 1.0R y
{
  size_t_forget_u a;
  size_t_write_uninit_u a y
}

ghost fn float32_t_forget_u (a: ptr) (#x: float32)
  requires elem_pts_to float32_t_ctype float32_t_repr a 1.0R x
  ensures  bytes_uninit float32_t_ctype a (SZ.v float32_t_sizeof)
{
  unfold elem_pts_to float32_t_ctype float32_t_repr a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  float32_t_repr_len x b;
  fold bytes_uninit float32_t_ctype a (SZ.v float32_t_sizeof);
}

fn float32_t_read_u (a: ptr) (#p: perm) (#x: erased float32)
  preserves elem_pts_to float32_t_ctype float32_t_repr a p x
  returns  y : float32
  ensures  rewrites_to y (reveal x)
{
  elem_reveal float32_t_ctype float32_t_repr a;
  with b e. assert (mem_pts_to_at a p b e);
  float32_t_repr_no_prov (reveal x) b;
  let y = I.float32_t_read_at a #p #x #(hide b) #e;
  elem_conceal float32_t_ctype float32_t_repr a #p #b #(reveal x) #e;
  y
}

fn float32_t_write_uninit_u (a: ptr) (y: float32)
  requires bytes_uninit float32_t_ctype a (SZ.v float32_t_sizeof)
  ensures  elem_pts_to float32_t_ctype float32_t_repr a 1.0R y
{
  unfold bytes_uninit float32_t_ctype a (SZ.v float32_t_sizeof);
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v float32_t_sizeof) None (float32_bits y);
  float32_t_repr_no_prov y b;
  EM.store a (hide float32_t_ctype) b;
  ET.store_read_ok e float32_t_ctype;
  elem_conceal float32_t_ctype float32_t_repr a #1.0R #b #y #(EM.store_index e float32_t_ctype)
}

fn float32_t_write_u (a: ptr) (y: float32) (#x: erased float32)
  requires elem_pts_to float32_t_ctype float32_t_repr a 1.0R x
  ensures  elem_pts_to float32_t_ctype float32_t_repr a 1.0R y
{
  float32_t_forget_u a;
  float32_t_write_uninit_u a y
}

ghost fn float64_t_forget_u (a: ptr) (#x: float64)
  requires elem_pts_to float64_t_ctype float64_t_repr a 1.0R x
  ensures  bytes_uninit float64_t_ctype a (SZ.v float64_t_sizeof)
{
  unfold elem_pts_to float64_t_ctype float64_t_repr a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  float64_t_repr_len x b;
  fold bytes_uninit float64_t_ctype a (SZ.v float64_t_sizeof);
}

fn float64_t_read_u (a: ptr) (#p: perm) (#x: erased float64)
  preserves elem_pts_to float64_t_ctype float64_t_repr a p x
  returns  y : float64
  ensures  rewrites_to y (reveal x)
{
  elem_reveal float64_t_ctype float64_t_repr a;
  with b e. assert (mem_pts_to_at a p b e);
  float64_t_repr_no_prov (reveal x) b;
  let y = I.float64_t_read_at a #p #x #(hide b) #e;
  elem_conceal float64_t_ctype float64_t_repr a #p #b #(reveal x) #e;
  y
}

fn float64_t_write_uninit_u (a: ptr) (y: float64)
  requires bytes_uninit float64_t_ctype a (SZ.v float64_t_sizeof)
  ensures  elem_pts_to float64_t_ctype float64_t_repr a 1.0R y
{
  unfold bytes_uninit float64_t_ctype a (SZ.v float64_t_sizeof);
  with old e. assert (mem_pts_to_at a 1.0R old e);
  let b = Enc.encode (SZ.v float64_t_sizeof) None (float64_bits y);
  float64_t_repr_no_prov y b;
  EM.store a (hide float64_t_ctype) b;
  ET.store_read_ok e float64_t_ctype;
  elem_conceal float64_t_ctype float64_t_repr a #1.0R #b #y #(EM.store_index e float64_t_ctype)
}

fn float64_t_write_u (a: ptr) (y: float64) (#x: erased float64)
  requires elem_pts_to float64_t_ctype float64_t_repr a 1.0R x
  ensures  elem_pts_to float64_t_ctype float64_t_repr a 1.0R y
{
  float64_t_forget_u a;
  float64_t_write_uninit_u a y
}

ghost fn ptr_forget_u (a: ptr) (#x: ptr)
  requires elem_pts_to ptr_ctype ptr_repr a 1.0R x
  ensures  bytes_uninit ptr_ctype a (SZ.v ptr_sizeof)
{
  unfold elem_pts_to ptr_ctype ptr_repr a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  ptr_repr_len x b;
  fold bytes_uninit ptr_ctype a (SZ.v ptr_sizeof);
}

fn ptr_read_u (a: ptr) (#p: perm) (#x: erased ptr)
  preserves elem_pts_to ptr_ctype ptr_repr a p x
  returns  y : ptr
  ensures  rewrites_to y (reveal x)
{
  elem_reveal ptr_ctype ptr_repr a;
  with b e. assert (mem_pts_to_at a p b e);
  ptr_repr_len (reveal x) b;
  let y = I.ptr_read_at a #p #x #(hide b) #e;
  elem_conceal ptr_ctype ptr_repr a #p #b #(reveal x) #e;
  y
}

fn ptr_write_uninit_u (a: ptr) (y: ptr)
  requires bytes_uninit ptr_ctype a (SZ.v ptr_sizeof)
  ensures  elem_pts_to ptr_ctype ptr_repr a 1.0R y
{
  unfold bytes_uninit ptr_ctype a (SZ.v ptr_sizeof);
  with old e. assert (mem_pts_to_at a 1.0R old e);
  I.ptr_store a y;
  ET.store_read_ok e ptr_ctype;
  elem_conceal ptr_ctype ptr_repr a #1.0R #(Enc.encode (SZ.v ptr_sizeof) (prov_of y) (addr_of y)) #y #(EM.store_index e ptr_ctype)
}

fn ptr_write_u (a: ptr) (y: ptr) (#x: erased ptr)
  requires elem_pts_to ptr_ctype ptr_repr a 1.0R x
  ensures  elem_pts_to ptr_ctype ptr_repr a 1.0R y
{
  ptr_forget_u a;
  ptr_write_uninit_u a y
}

