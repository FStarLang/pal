module Pulse.Lib.C.Palow.Machine.Intrinsics

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Array
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.Float
open Pulse.Lib.C.Palow.CTypes

module ET = Pulse.Lib.C.Palow.Etype
module EM = Pulse.Lib.C.Palow.Effective.Machine
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64

(* Pointer provenance and addresses are ghost observations. The machine gets
   the runtime pointer, rather than trying to compute a ghost byte payload. *)
fn ptr_store (a: ptr) (y: ptr) (#old: erased bytes)
             (#e: ET.etypes { ET.elen e == ET.csize ptr_ctype })
  requires mem_pts_to_at a 1.0R old e
  requires pure (len old == ET.csize ptr_ctype /\ ET.read_ok e ptr_ctype)
  ensures mem_pts_to_at a 1.0R
    (Pulse.Lib.C.Palow.Encoding.encode (SZ.v ptr_sizeof) (prov_of y) (addr_of y))
    (EM.store_index e ptr_ctype)


(* Actual scalar loads and stack destruction. Typed writes are implemented
   using the indexed machine store, never a byte-preserving ghost relabel. *)




fn uint32_t_stack_free (a: ptr)
  requires uint32_t_pts_to_uninit a

fn ptr_stack_free (a: ptr)
  requires ptr_pts_to_uninit a


fn bool_t_stack_free (a: ptr)
  requires bool_t_pts_to_uninit a


fn int8_t_stack_free (a: ptr)
  requires int8_t_pts_to_uninit a


fn int16_t_stack_free (a: ptr)
  requires int16_t_pts_to_uninit a


fn int32_t_stack_free (a: ptr)
  requires int32_t_pts_to_uninit a


fn int64_t_stack_free (a: ptr)
  requires int64_t_pts_to_uninit a

fn uint8_t_stack_free (a: ptr)
  requires uint8_t_pts_to_uninit a


fn uint16_t_stack_free (a: ptr)
  requires uint16_t_pts_to_uninit a


fn uint64_t_stack_free (a: ptr)
  requires uint64_t_pts_to_uninit a


fn size_t_stack_free (a: ptr)
  requires size_t_pts_to_uninit a


fn float32_t_stack_free (a: ptr)
  requires float32_t_pts_to_uninit a


fn float64_t_stack_free (a: ptr)
  requires float64_t_pts_to_uninit a

fn mem_stack_free (a: ptr) (#b: erased bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e













fn uint32_t_read_at (a: ptr) (#p: perm) (#x: erased U32.t)
                     (#b: erased bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires pure (uint32_t_repr x b /\ len b == ET.csize uint32_t_ctype /\
                 ET.elen e == len b /\ ET.read_ok e uint32_t_ctype /\ initialized b)
  returns y: U32.t
  ensures rewrites_to y (reveal x)


fn uint8_t_read_at (a: ptr) (#p: perm) (#x: erased U8.t)
                     (#b: erased bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires pure (uint8_t_repr x b /\ len b == ET.csize uint8_t_ctype /\
                 ET.elen e == len b /\ ET.read_ok e uint8_t_ctype /\ initialized b)
  returns y: U8.t
  ensures rewrites_to y (reveal x)


fn ptr_read_at (a: ptr) (#p: perm) (#x: erased ptr)
                     (#b: erased bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires pure (ptr_repr x b /\ len b == ET.csize ptr_ctype /\
                 ET.elen e == len b /\ ET.read_ok e ptr_ctype /\ initialized b)
  returns y: ptr
  ensures rewrites_to y (reveal x)


fn bool_t_read_at (a: ptr) (#p: perm) (#x: erased bool)
                     (#b: erased bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires pure (bool_t_repr x b /\ len b == ET.csize bool_t_ctype /\
                 ET.elen e == len b /\ ET.read_ok e bool_t_ctype /\ initialized b)
  returns y: bool
  ensures rewrites_to y (reveal x)


fn int8_t_read_at (a: ptr) (#p: perm) (#x: erased I8.t)
                     (#b: erased bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires pure (int8_t_repr x b /\ len b == ET.csize int8_t_ctype /\
                 ET.elen e == len b /\ ET.read_ok e int8_t_ctype /\ initialized b)
  returns y: I8.t
  ensures rewrites_to y (reveal x)


fn int16_t_read_at (a: ptr) (#p: perm) (#x: erased I16.t)
                     (#b: erased bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires pure (int16_t_repr x b /\ len b == ET.csize int16_t_ctype /\
                 ET.elen e == len b /\ ET.read_ok e int16_t_ctype /\ initialized b)
  returns y: I16.t
  ensures rewrites_to y (reveal x)


fn int32_t_read_at (a: ptr) (#p: perm) (#x: erased I32.t)
                     (#b: erased bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires pure (int32_t_repr x b /\ len b == ET.csize int32_t_ctype /\
                 ET.elen e == len b /\ ET.read_ok e int32_t_ctype /\ initialized b)
  returns y: I32.t
  ensures rewrites_to y (reveal x)


fn int64_t_read_at (a: ptr) (#p: perm) (#x: erased I64.t)
                     (#b: erased bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires pure (int64_t_repr x b /\ len b == ET.csize int64_t_ctype /\
                 ET.elen e == len b /\ ET.read_ok e int64_t_ctype /\ initialized b)
  returns y: I64.t
  ensures rewrites_to y (reveal x)


fn uint16_t_read_at (a: ptr) (#p: perm) (#x: erased U16.t)
                     (#b: erased bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires pure (uint16_t_repr x b /\ len b == ET.csize uint16_t_ctype /\
                 ET.elen e == len b /\ ET.read_ok e uint16_t_ctype /\ initialized b)
  returns y: U16.t
  ensures rewrites_to y (reveal x)


fn uint64_t_read_at (a: ptr) (#p: perm) (#x: erased U64.t)
                     (#b: erased bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires pure (uint64_t_repr x b /\ len b == ET.csize uint64_t_ctype /\
                 ET.elen e == len b /\ ET.read_ok e uint64_t_ctype /\ initialized b)
  returns y: U64.t
  ensures rewrites_to y (reveal x)


fn size_t_read_at (a: ptr) (#p: perm) (#x: erased SZ.t)
                     (#b: erased bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires pure (size_t_repr x b /\ len b == ET.csize size_t_ctype /\
                 ET.elen e == len b /\ ET.read_ok e size_t_ctype /\ initialized b)
  returns y: SZ.t
  ensures rewrites_to y (reveal x)


fn float32_t_read_at (a: ptr) (#p: perm) (#x: erased float32)
                     (#b: erased bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires pure (float32_t_repr x b /\ len b == ET.csize float32_t_ctype /\
                 ET.elen e == len b /\ ET.read_ok e float32_t_ctype /\ initialized b)
  returns y: float32
  ensures rewrites_to y (reveal x)


fn float64_t_read_at (a: ptr) (#p: perm) (#x: erased float64)
                     (#b: erased bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires pure (float64_t_repr x b /\ len b == ET.csize float64_t_ctype /\
                 ET.elen e == len b /\ ET.read_ok e float64_t_ctype /\ initialized b)
  returns y: float64
  ensures rewrites_to y (reveal x)


fn ptr_initialize (a: ptr) (y: ptr)
  requires Pulse.Lib.C.Palow.Effective.prepared a ptr_ctype
  ensures mem_pts_to_at a 1.0R
    (Pulse.Lib.C.Palow.Encoding.encode (SZ.v ptr_sizeof) (prov_of y) (addr_of y))
    (ET.etypes_of ptr_ctype false)
