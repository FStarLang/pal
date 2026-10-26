module Pulse.Lib.C.Palow.Union

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow.Encoding
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.Aggregate

module SZ = FStar.SizeT
module Seq = FStar.Seq
module U32 = FStar.UInt32
module ET = Pulse.Lib.C.Palow.Etype
module V = Pulse.Lib.C.Palow.Effective.Value
module EM = Pulse.Lib.C.Palow.Effective.Machine
module I = Pulse.Lib.C.Palow.Machine.Intrinsics

noeq type union_U =
  | U_x : U32.t -> union_U
  | U_t : struct_T -> union_U

let union_U_sizeof : SZ.t = 8sz
let union_U_alignof : SZ.t = 4sz
let union_U_ctype : ET.ctype =
  ET.TUnion "union_U" 8 [(0, uint32_t_ctype); (0, struct_T_ctype)]

let union_U_repr (u: union_U) (b: bytes) : prop =
  len b == 8 /\ (len b == 8 ==>
    (match u with
     | U_x v -> uint32_t_repr v (slice b 0 4)
     | U_t t -> struct_T_repr t b))

let union_U_pts_to_at ([@@@mkey] a: ptr) (p: perm) (u: union_U) (e: ET.etypes) : slprop =
  V.value union_U_ctype union_U_repr union_U_alignof a p u e

let union_U_pts_to ([@@@mkey] a: ptr) (p: perm) (u: union_U) : slprop =
  exists* (e: ET.etypes { ET.elen e == 8 }). union_U_pts_to_at a p u e

let union_U_member_aligned (a: ptr)
  : Lemma (requires aligned a union_U_alignof)
          (ensures aligned a uint32_t_alignof /\ aligned a struct_T_alignof) = ()

let union_U_x_rest ([@@@mkey] a: ptr) (p: perm)
                   (e: ET.etypes { ET.elen e == 8 }) : slprop =
  exists* b. mem_pts_to_at (a +! 4sz) p b (Seq.slice e 4 8) ** pure (len b == 4)

let union_U_x_view ([@@@mkey] a: ptr) (p: perm) (v: U32.t)
                   (e: ET.etypes { ET.elen e == 8 }) : slprop =
  V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a p v (Seq.slice e 0 4)
  ** union_U_x_rest a p e
  ** pure (ET.read_ok e union_U_ctype /\ aligned a union_U_alignof)

let union_U_t_view ([@@@mkey] a: ptr) (p: perm) (t: struct_T)
                   (e: ET.etypes { ET.elen e == 8 }) : slprop =
  struct_T_pts_to_at a p t e ** pure (ET.read_ok e union_U_ctype)

ghost fn union_U_split_x_at (a: ptr) (#p: perm) (#v: U32.t)
                            (#e: ET.etypes { ET.elen e == 8 })
  requires union_U_pts_to_at a p (U_x v) e
  ensures union_U_x_view a p v e
{
  unfold union_U_pts_to_at a p (U_x v) e;
  V.reveal_value union_U_ctype union_U_repr union_U_alignof a;
  with b. assert (mem_pts_to_at a p b e);
  union_U_member_aligned a;
  ET.read_ok_slice e union_U_ctype 0 uint32_t_ctype;
  mem_split_at a 4sz;
  V.claim uint32_t_ctype uint32_t_repr uint32_t_alignof a #p #v;
  fold union_U_x_rest a p e;
  fold union_U_x_view a p v e;
}

ghost fn union_U_join_x_at (a: ptr) (#p: perm) (#v: U32.t)
                           (#e: ET.etypes { ET.elen e == 8 })
  requires union_U_x_view a p v e
  ensures union_U_pts_to_at a p (U_x v) e
{
  unfold union_U_x_view a p v e;
  V.reveal_value uint32_t_ctype uint32_t_repr uint32_t_alignof a;
  with b. assert (mem_pts_to_at a p b (Seq.slice e 0 4));
  unfold union_U_x_rest a p e;
  with rest. assert (mem_pts_to_at (a +! 4sz) p rest (Seq.slice e 4 8));
  mem_join_at a #p #b #rest #(Seq.slice e 0 4) #(Seq.slice e 4 8) 4sz;
  Seq.lemma_eq_intro (Seq.append (Seq.slice e 0 4) (Seq.slice e 4 8)) e;
  append_slice_left b rest;
  V.claim union_U_ctype union_U_repr union_U_alignof a #p #(U_x v);
  fold union_U_pts_to_at a p (U_x v) e;
}

ghost fn union_U_split_x (a: ptr) (#p: perm) (#v: U32.t)
  requires union_U_pts_to a p (U_x v)
  ensures exists* (e: ET.etypes { ET.elen e == 8 }). union_U_x_view a p v e
{
  unfold union_U_pts_to a p (U_x v);
  with e. assert (union_U_pts_to_at a p (U_x v) e);
  union_U_split_x_at a;
}

ghost fn union_U_join_x (a: ptr) (#p: perm) (#v: U32.t)
                        (#e: ET.etypes { ET.elen e == 8 })
  requires union_U_x_view a p v e
  ensures union_U_pts_to a p (U_x v)
{
  union_U_join_x_at a;
  fold union_U_pts_to a p (U_x v);
}

ghost fn union_U_split_t_at (a: ptr) (#p: perm) (#t: struct_T)
                            (#e: ET.etypes { ET.elen e == 8 })
  requires union_U_pts_to_at a p (U_t t) e
  ensures union_U_t_view a p t e
{
  unfold union_U_pts_to_at a p (U_t t) e;
  V.reveal_value union_U_ctype union_U_repr union_U_alignof a;
  with b. assert (mem_pts_to_at a p b e);
  union_U_member_aligned a;
  ET.read_ok_slice e union_U_ctype 0 struct_T_ctype;
  Seq.lemma_eq_intro (Seq.slice e 0 8) e;
  V.claim struct_T_ctype struct_T_repr struct_T_alignof a #p #t #b #e;
  fold struct_T_pts_to_at a p t e;
  fold union_U_t_view a p t e;
}

ghost fn union_U_join_t_at (a: ptr) (#p: perm) (#t: struct_T)
                           (#e: ET.etypes { ET.elen e == 8 })
  requires union_U_t_view a p t e
  ensures union_U_pts_to_at a p (U_t t) e
{
  unfold union_U_t_view a p t e;
  unfold struct_T_pts_to_at a p t e;
  V.reveal_value struct_T_ctype struct_T_repr struct_T_alignof a;
  with b. assert (mem_pts_to_at a p b e);
  V.claim union_U_ctype union_U_repr union_U_alignof a #p #(U_t t) #b #e;
  fold union_U_pts_to_at a p (U_t t) e;
}

ghost fn union_U_split_t (a: ptr) (#p: perm) (#t: struct_T)
  requires union_U_pts_to a p (U_t t)
  ensures exists* (e: ET.etypes { ET.elen e == 8 }). union_U_t_view a p t e
{
  unfold union_U_pts_to a p (U_t t);
  with e. assert (union_U_pts_to_at a p (U_t t) e);
  union_U_split_t_at a;
}

ghost fn union_U_join_t (a: ptr) (#p: perm) (#t: struct_T)
                        (#e: ET.etypes { ET.elen e == 8 })
  requires union_U_t_view a p t e
  ensures union_U_pts_to a p (U_t t)
{
  union_U_join_t_at a;
  fold union_U_pts_to a p (U_t t);
}

let union_U_pun (v w: U32.t) (b: bytes)
  : Lemma (requires union_U_repr (U_x v) b /\ uint32_t_repr w (slice b 4 8))
          (ensures union_U_repr (U_t ({ y = v; z = w })) b) = ()

ghost fn union_U_focus_t_y (a: ptr) (#p: perm) (#v: U32.t)
  requires uint32_t_pts_to a p v
  ensures uint32_t_pts_to (a +! struct_T_offsetof_y) p v
{
  rewrite (uint32_t_pts_to a p v) as (uint32_t_pts_to (a +! struct_T_offsetof_y) p v);
}

ghost fn union_U_unfocus_t_y (a: ptr) (#p: perm) (#v: U32.t)
  requires uint32_t_pts_to (a +! struct_T_offsetof_y) p v
  ensures uint32_t_pts_to a p v
{
  rewrite (uint32_t_pts_to (a +! struct_T_offsetof_y) p v) as (uint32_t_pts_to a p v);
}

(* A member store preserves nominal union labels only if they were already
   present. It never establishes a union from a scalar store into None bytes. *)
#push-options "--z3rlimit 40"
fn union_U_store_x (a: ptr) (v: U32.t) (#old: erased (b: bytes { len b == 8 }))
                   (#e: ET.etypes { ET.elen e == 8 })
  requires mem_pts_to_at a 1.0R old e
  requires pure (len old == 8 /\ ET.read_ok e union_U_ctype /\
    (forall (k: nat). k < 8 ==> Some? (ET.eget e k)))
  ensures mem_pts_to_at a 1.0R
    (append (encode 4 None (U32.v v)) (slice old 4 8)) e
{
  ET.read_ok_slice e union_U_ctype 0 uint32_t_ctype;
  ET.store_readable_stable (Seq.slice e 0 4) uint32_t_ctype;
  mem_split_at a 4sz;
  let b = encode 4 None (U32.v v);
  uint32_t_repr_no_prov v b;
  EM.store a (hide uint32_t_ctype) b;
  rewrite (mem_pts_to_at a 1.0R b (EM.store_index (Seq.slice e 0 4) uint32_t_ctype))
    as (mem_pts_to_at a 1.0R b (Seq.slice e 0 4));
  mem_join_at a #1.0R #b #(slice old 4 8) #(Seq.slice e 0 4) #(Seq.slice e 4 8) 4sz;
  Seq.lemma_eq_intro (Seq.append (Seq.slice e 0 4) (Seq.slice e 4 8)) e;
  assert (pure (Seq.append (Seq.slice e 0 4) (Seq.slice e 4 8) == e));
  rewrite (mem_pts_to_at a 1.0R (append b (slice old 4 8))
    (Seq.append (Seq.slice e 0 4) (Seq.slice e 4 8)))
    as (mem_pts_to_at a 1.0R (append b (slice old 4 8)) e);
}

fn union_U_read_x (a: ptr) (#p: perm) (#v: erased U32.t)
                  (#old: erased bytes) (#e: ET.etypes { ET.elen e == 8 })
  preserves mem_pts_to_at a p old e
  requires pure (union_U_repr (U_x (reveal v)) old /\ ET.read_ok e union_U_ctype)
  returns r: U32.t
  ensures rewrites_to r (reveal v)
{
  ET.read_ok_slice e union_U_ctype 0 uint32_t_ctype;
  mem_split_at a 4sz;
  uint32_t_repr_no_prov (reveal v) (slice old 0 4);
  let r = I.uint32_t_read_at a #p #v #(hide (slice old 0 4)) #(Seq.slice e 0 4);
  mem_join_at a #p #(slice old 0 4) #(slice old 4 8)
    #(Seq.slice e 0 4) #(Seq.slice e 4 8) 4sz;
  Seq.lemma_eq_intro (append (slice old 0 4) (slice old 4 8)) (reveal old);
  Seq.lemma_eq_intro (Seq.append (Seq.slice e 0 4) (Seq.slice e 4 8)) e;
  r
}

fn union_pun_test (a: ptr) (#u0: erased union_U)
                  (#e: ET.etypes { ET.elen e == 8 })
  requires union_U_pts_to_at a 1.0R u0 e
  requires pure (forall (k: nat). k < 8 ==> Some? (ET.eget e k))
  returns r: U32.t
  ensures union_U_pts_to_at a 1.0R (U_x 10ul) e ** pure (r == 10ul)
{
  unfold union_U_pts_to_at a 1.0R u0 e;
  V.reveal_value union_U_ctype union_U_repr union_U_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  union_U_store_x a 10ul;
  let b: erased bytes = hide (append (encode 4 None 10) (slice old 4 8));
  append_slice_left (encode 4 None 10) (slice old 4 8);
  let r = union_U_read_x a #1.0R #(hide 10ul) #b #e;
  V.claim union_U_ctype union_U_repr union_U_alignof a #1.0R #(U_x 10ul);
  fold union_U_pts_to_at a 1.0R (U_x 10ul) e;
  r
}

fn union_pun_test_struct (a: ptr) (#t0: erased struct_T)
                         (#e: ET.etypes { ET.elen e == 8 })
  requires union_U_pts_to_at a 1.0R (U_t t0) e
  requires pure (forall (k: nat). k < 8 ==> Some? (ET.eget e k))
  returns r: U32.t
  ensures union_U_pts_to_at a 1.0R (U_t ({ y = 10ul; z = (reveal t0).z })) e
    ** pure (r == 10ul)
{
  unfold union_U_pts_to_at a 1.0R (U_t t0) e;
  V.reveal_value union_U_ctype union_U_repr union_U_alignof a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  union_U_store_x a 10ul;
  let b: erased bytes = hide (append (encode 4 None 10) (slice old 4 8));
  append_slice_left (encode 4 None 10) (slice old 4 8);
  append_slice_right (encode 4 None 10) (slice old 4 8);
  let r = union_U_read_x a #1.0R #(hide 10ul) #b #e;
  struct_T_repr_intro ({ y = 10ul; z = (reveal t0).z })
    (encode 4 None 10) (slice old 4 8);
  V.claim union_U_ctype union_U_repr union_U_alignof a #1.0R
    #(U_t ({ y = 10ul; z = (reveal t0).z }));
  fold union_U_pts_to_at a 1.0R (U_t ({ y = 10ul; z = (reveal t0).z })) e;
  r
}
#pop-options
