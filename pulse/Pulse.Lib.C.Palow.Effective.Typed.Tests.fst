module Pulse.Lib.C.Palow.Effective.Typed.Tests

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.Aggregate

module ET = Pulse.Lib.C.Palow.Etype
module V = Pulse.Lib.C.Palow.Effective.Value
module M = Pulse.Lib.C.Palow.Machine
module EM = Pulse.Lib.C.Palow.Effective.Machine
module E = Pulse.Lib.C.Palow.Effective
module Enc = Pulse.Lib.C.Palow.Encoding
module Seq = FStar.Seq
module U32 = FStar.UInt32
module Alloc = Pulse.Lib.C.Palow.Alloc

(* This is the generator's direct-field pattern. The enclosing labels remain
   tied to their resource throughout the read and the compatible store. *)
fn struct_field_update (a: ptr) (y: U32.t) (#x: erased struct_T)
                       (#e: ET.etypes { ET.elen e == 8 })
  requires struct_T_pts_to_at a 1.0R x e
  requires pure (forall (k: nat). k < 8 ==> Some? (ET.eget e k))
  ensures struct_T_pts_to_at a 1.0R ({ y = y; z = (reveal x).z }) e
{
  struct_T_split_at a;
  unfold struct_T_fields a 1.0R x e;
  let old = M.uint32_t_read_at a;
  V.forget uint32_t_ctype uint32_t_repr uint32_t_alignof a;
  M.uint32_t_write_existing a y;
  fold struct_T_fields a 1.0R ({ y = y; z = (reveal x).z }) e;
  struct_T_join_at a;
}

(* Unlike member stores into None bytes, a genuine whole-object
   initialization can establish the nominal allocated aggregate. *)
fn struct_initialize (a: ptr) (x: struct_T)
  requires E.prepared a struct_T_ctype
  requires pure (aligned a struct_T_alignof)
  ensures exists* e. struct_T_pts_to_at a 1.0R x e
    ** pure (e == ET.etypes_of struct_T_ctype false)
{
  let b_y = Enc.encode 4 None (U32.v x.y);
  let bz = Enc.encode 4 None (U32.v x.z);
  let b = append b_y bz;
  struct_T_repr_intro x b_y bz;
  EM.initialize a (hide struct_T_ctype) b;
  with e. assert (mem_pts_to_at a 1.0R b e);
  assert (pure (e == ET.etypes_of struct_T_ctype false));
  V.claim struct_T_ctype struct_T_repr struct_T_alignof a #1.0R #x #b #e;
  fold struct_T_pts_to_at a 1.0R x e;
}

fn character_store_no_type (a: ptr) (x: FStar.UInt8.t)
  requires V.storage uint8_t_ctype uint8_t_alignof a (Seq.create 1 None)
  ensures V.value uint8_t_ctype uint8_t_repr uint8_t_alignof a 1.0R x
    (Seq.create 1 None)
{
  M.uint8_t_write_uninit_at a x;
}

(* The allocation wrapper retains the free token, but still demands actual
   full_mutable evidence. An allocation token alone does not prove that fact. *)
fn prepare_and_free (a: ptr) (n: FStar.SizeT.t) (ct: ET.ctype)
                    (#b: erased bytes) (#e: ET.etypes)
  requires Alloc.freeable a n ** mem_pts_to_at a 1.0R b e
  requires pure (len b == FStar.SizeT.v n /\ ET.elen e == len b /\
                 FStar.SizeT.v n == ET.csize ct /\ ET.full_mutable e)
{
  E.prepare_allocation a n ct;
  EM.free_prepared a (hide ct) #(hide n);
}

fn prepare_and_store (a: ptr) (x: U32.t) (#b: erased bytes) (#e: ET.etypes)
  requires Alloc.freeable a 4sz ** mem_pts_to_at a 1.0R b e
  requires pure (len b == 4 /\ ET.elen e == 4 /\ aligned a uint32_t_alignof /\
                 ET.full_mutable e)
  ensures Alloc.freeable a 4sz
    ** (exists* e1. V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a 1.0R x e1
      ** pure (e1 == ET.etypes_of uint32_t_ctype false))
{
  E.prepare_allocation a 4sz uint32_t_ctype;
  M.uint32_t_initialize_at a x;
}

let mixed_mutable_is_not_nominal ()
  : Lemma (
    let e = Seq.append (ET.etypes_of uint32_t_ctype false) (Seq.create 4 None) in
    ET.all_mutable e /\ not (ET.full_mutable e) /\ not (ET.read_ok e struct_T_ctype))
  = ()
