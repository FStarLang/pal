module Pulse.Lib.C.Palow.Aggregate

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow.Encoding
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.Array
open Pulse.Lib.C.Palow.Machine

module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module ET = Pulse.Lib.C.Palow.Etype
module V = Pulse.Lib.C.Palow.Effective.Value

noeq type struct_S = { f: U32.t; g: U8.t }

let struct_S_sizeof : SZ.t = 8sz
let struct_S_alignof : SZ.t = 4sz
let struct_S_offsetof_f : SZ.t = 0sz
let struct_S_offsetof_g : SZ.t = 4sz
let struct_S_padoff : SZ.t = 5sz
let struct_S_padlen : SZ.t = 3sz
let struct_S_ctype : ET.ctype =
  ET.TStruct "struct_S" 8 [(0, uint32_t_ctype); (4, uint8_t_ctype)]

let struct_S_repr (x: struct_S) (b: bytes) : prop =
  len b == 8 /\ (len b == 8 ==>
    uint32_t_repr x.f (slice b 0 4) /\ uint8_t_repr x.g (slice b 4 5))

let struct_S_pts_to_at ([@@@mkey] a: ptr) (p: perm) (x: struct_S) (e: ET.etypes) : slprop =
  V.value struct_S_ctype struct_S_repr struct_S_alignof a p x e

let struct_S_pts_to ([@@@mkey] a: ptr) (p: perm) (x: struct_S) : slprop =
  exists* (e: ET.etypes { ET.elen e == 8 }). struct_S_pts_to_at a p x e

let struct_S_padding ([@@@mkey] a: ptr) (p: perm)
                     (e: ET.etypes { ET.elen e == 8 }) : slprop =
  exists* pad. mem_pts_to_at (a +! 5sz) p pad (Seq.slice e 5 8)
    ** pure (len pad == 3)

(* A field view remembers the enclosing index and nominal access evidence.
   Independently labelled scalar fields cannot be folded into this view. *)
let struct_S_fields ([@@@mkey] a: ptr) (p: perm) (x: struct_S)
                    (e: ET.etypes { ET.elen e == 8 }) : slprop =
  V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a p x.f (Seq.slice e 0 4)
  ** V.value uint8_t_ctype uint8_t_repr uint8_t_alignof (a +! 4sz) p x.g (Seq.slice e 4 5)
  ** struct_S_padding a p e
  ** pure (ET.read_ok e struct_S_ctype /\ aligned a struct_S_alignof)

let struct_S_repr_elim (x: struct_S) (b: bytes)
  : Lemma (requires struct_S_repr x b)
          (ensures len b == 8 /\
            slice b 0 4 == encode 4 None (U32.v x.f) /\
            slice b 4 5 == encode 1 None (U8.v x.g)) = ()

let struct_S_repr_intro (x: struct_S) (bf bg bpad: bytes)
  : Lemma (requires uint32_t_repr x.f bf /\ uint8_t_repr x.g bg /\ len bpad == 3)
          (ensures struct_S_repr x (append bf (append bg bpad)))
  = let b = append bf (append bg bpad) in
    Seq.lemma_eq_intro (slice b 0 4) bf;
    Seq.lemma_eq_intro (slice b 4 5) bg

let struct_S_padptr (a: ptr)
  : Lemma ((a +! 4sz) +! 1sz == a +! struct_S_padoff)
  = addr_of_add a 4sz;
    addr_of_add (a +! 4sz) 1sz;
    addr_of_add a struct_S_padoff;
    ptr_ext ((a +! 4sz) +! 1sz) (a +! struct_S_padoff)

let struct_S_field_aligned (a: ptr)
  : Lemma (requires aligned a struct_S_alignof)
          (ensures aligned a uint32_t_alignof /\ aligned (a +! 4sz) uint8_t_alignof) = ()

#push-options "--z3rlimit 40"
ghost fn struct_S_split_at (a: ptr) (#p: perm) (#x: struct_S)
                           (#e: ET.etypes { ET.elen e == 8 })
  requires struct_S_pts_to_at a p x e
  ensures struct_S_fields a p x e
{
  unfold struct_S_pts_to_at a p x e;
  V.reveal_value struct_S_ctype struct_S_repr struct_S_alignof a;
  with b. assert (mem_pts_to_at a p b e);
  struct_S_repr_elim x b;
  struct_S_field_aligned a;
  ET.read_ok_slice e struct_S_ctype 0 uint32_t_ctype;
  ET.read_ok_slice e struct_S_ctype 4 uint8_t_ctype;
  mem_split_at a 4sz;
  V.claim uint32_t_ctype uint32_t_repr uint32_t_alignof a #p #x.f;
  mem_split_at (a +! 4sz) 1sz;
  Seq.slice_slice b 4 8 0 1;
  Seq.slice_slice e 4 8 0 1;
  V.claim uint8_t_ctype uint8_t_repr uint8_t_alignof (a +! 4sz) #p #x.g;
  Seq.slice_slice b 4 8 1 4;
  Seq.slice_slice e 4 8 1 4;
  struct_S_padptr a;
  rewrite (mem_pts_to_at ((a +! 4sz) +! 1sz) p
    (slice (slice b 4 8) 1 4) (Seq.slice (Seq.slice e 4 8) 1 4))
    as (mem_pts_to_at (a +! 5sz) p (slice b 5 8) (Seq.slice e 5 8));
  rewrite (V.value uint8_t_ctype uint8_t_repr uint8_t_alignof (a +! 4sz) p x.g
    (Seq.slice (Seq.slice e 4 8) 0 1))
    as (V.value uint8_t_ctype uint8_t_repr uint8_t_alignof (a +! 4sz) p x.g
      (Seq.slice e 4 5));
  fold struct_S_padding a p e;
  fold struct_S_fields a p x e;
}

ghost fn struct_S_join_at (a: ptr) (#p: perm) (#x: struct_S)
                          (#e: ET.etypes { ET.elen e == 8 })
  requires struct_S_fields a p x e
  ensures struct_S_pts_to_at a p x e
{
  unfold struct_S_fields a p x e;
  V.reveal_value uint32_t_ctype uint32_t_repr uint32_t_alignof a;
  with bf. assert (mem_pts_to_at a p bf (Seq.slice e 0 4));
  V.reveal_value uint8_t_ctype uint8_t_repr uint8_t_alignof (a +! 4sz);
  with bg. assert (mem_pts_to_at (a +! 4sz) p bg (Seq.slice e 4 5));
  unfold struct_S_padding a p e;
  with pad. assert (mem_pts_to_at (a +! 5sz) p pad (Seq.slice e 5 8));
  struct_S_padptr a;
  rewrite (mem_pts_to_at (a +! 5sz) p pad (Seq.slice e 5 8))
    as (mem_pts_to_at ((a +! 4sz) +! 1sz) p pad (Seq.slice e 5 8));
  mem_join_at (a +! 4sz) #p #bg #pad #(Seq.slice e 4 5) #(Seq.slice e 5 8) 1sz;
  mem_join_at a #p #bf #(append bg pad) #(Seq.slice e 0 4)
    #(Seq.append (Seq.slice e 4 5) (Seq.slice e 5 8)) 4sz;
  Seq.lemma_eq_intro (Seq.append (Seq.slice e 0 4)
    (Seq.append (Seq.slice e 4 5) (Seq.slice e 5 8))) e;
  struct_S_repr_intro x bf bg pad;
  V.claim struct_S_ctype struct_S_repr struct_S_alignof a #p #x;
  fold struct_S_pts_to_at a p x e;
}
#pop-options

ghost fn struct_S_split (a: ptr) (#p: perm) (#x: struct_S)
  requires struct_S_pts_to a p x
  ensures exists* (e: ET.etypes { ET.elen e == 8 }). struct_S_fields a p x e
{
  unfold struct_S_pts_to a p x;
  with e. assert (struct_S_pts_to_at a p x e);
  struct_S_split_at a;
}

ghost fn struct_S_join (a: ptr) (#p: perm) (#x: struct_S)
                       (#e: ET.etypes { ET.elen e == 8 })
  requires struct_S_fields a p x e
  ensures struct_S_pts_to a p x
{
  struct_S_join_at a;
  fold struct_S_pts_to a p x;
}

noeq type struct_T = { y: U32.t; z: U32.t }

let struct_T_sizeof : SZ.t = 8sz
let struct_T_alignof : SZ.t = 4sz
let struct_T_offsetof_y : SZ.t = 0sz
let struct_T_offsetof_z : SZ.t = 4sz
let struct_T_ctype : ET.ctype =
  ET.TStruct "struct_T" 8 [(0, uint32_t_ctype); (4, uint32_t_ctype)]

let struct_T_repr (x: struct_T) (b: bytes) : prop =
  len b == 8 /\ (len b == 8 ==>
    uint32_t_repr x.y (slice b 0 4) /\ uint32_t_repr x.z (slice b 4 8))

let struct_T_pts_to_at ([@@@mkey] a: ptr) (p: perm) (x: struct_T) (e: ET.etypes) : slprop =
  V.value struct_T_ctype struct_T_repr struct_T_alignof a p x e

let struct_T_pts_to ([@@@mkey] a: ptr) (p: perm) (x: struct_T) : slprop =
  exists* (e: ET.etypes { ET.elen e == 8 }). struct_T_pts_to_at a p x e

let struct_T_fields ([@@@mkey] a: ptr) (p: perm) (x: struct_T)
                    (e: ET.etypes { ET.elen e == 8 }) : slprop =
  V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a p x.y (Seq.slice e 0 4)
  ** V.value uint32_t_ctype uint32_t_repr uint32_t_alignof (a +! 4sz) p x.z (Seq.slice e 4 8)
  ** pure (ET.read_ok e struct_T_ctype /\ aligned a struct_T_alignof)

let struct_T_field_aligned (a: ptr)
  : Lemma (requires aligned a struct_T_alignof)
          (ensures aligned a uint32_t_alignof /\ aligned (a +! 4sz) uint32_t_alignof)
  = aligned_field a struct_T_alignof struct_T_offsetof_y uint32_t_alignof;
    aligned_field a struct_T_alignof struct_T_offsetof_z uint32_t_alignof

let struct_T_repr_intro (x: struct_T) (b_y bz: bytes)
  : Lemma (requires uint32_t_repr x.y b_y /\ uint32_t_repr x.z bz)
          (ensures struct_T_repr x (append b_y bz))
  = let b = append b_y bz in
    Seq.lemma_eq_intro (slice b 0 4) b_y;
    Seq.lemma_eq_intro (slice b 4 8) bz

ghost fn struct_T_split_at (a: ptr) (#p: perm) (#x: struct_T)
                           (#e: ET.etypes { ET.elen e == 8 })
  requires struct_T_pts_to_at a p x e
  ensures struct_T_fields a p x e
{
  unfold struct_T_pts_to_at a p x e;
  V.reveal_value struct_T_ctype struct_T_repr struct_T_alignof a;
  with b. assert (mem_pts_to_at a p b e);
  struct_T_field_aligned a;
  ET.read_ok_slice e struct_T_ctype 0 uint32_t_ctype;
  ET.read_ok_slice e struct_T_ctype 4 uint32_t_ctype;
  mem_split_at a 4sz;
  V.claim uint32_t_ctype uint32_t_repr uint32_t_alignof a #p #x.y;
  V.claim uint32_t_ctype uint32_t_repr uint32_t_alignof (a +! 4sz) #p #x.z;
  fold struct_T_fields a p x e;
}

ghost fn struct_T_join_at (a: ptr) (#p: perm) (#x: struct_T)
                          (#e: ET.etypes { ET.elen e == 8 })
  requires struct_T_fields a p x e
  ensures struct_T_pts_to_at a p x e
{
  unfold struct_T_fields a p x e;
  V.reveal_value uint32_t_ctype uint32_t_repr uint32_t_alignof a;
  with b_y. assert (mem_pts_to_at a p b_y (Seq.slice e 0 4));
  V.reveal_value uint32_t_ctype uint32_t_repr uint32_t_alignof (a +! 4sz);
  with bz. assert (mem_pts_to_at (a +! 4sz) p bz (Seq.slice e 4 8));
  mem_join_at a #p #b_y #bz #(Seq.slice e 0 4) #(Seq.slice e 4 8) 4sz;
  Seq.lemma_eq_intro (Seq.append (Seq.slice e 0 4) (Seq.slice e 4 8)) e;
  struct_T_repr_intro x b_y bz;
  V.claim struct_T_ctype struct_T_repr struct_T_alignof a #p #x;
  fold struct_T_pts_to_at a p x e;
}

ghost fn struct_T_split (a: ptr) (#p: perm) (#x: struct_T)
  requires struct_T_pts_to a p x
  ensures exists* (e: ET.etypes { ET.elen e == 8 }). struct_T_fields a p x e
{
  unfold struct_T_pts_to a p x;
  with e. assert (struct_T_pts_to_at a p x e);
  struct_T_split_at a;
}

ghost fn struct_T_join (a: ptr) (#p: perm) (#x: struct_T)
                       (#e: ET.etypes { ET.elen e == 8 })
  requires struct_T_fields a p x e
  ensures struct_T_pts_to a p x
{
  struct_T_join_at a;
  fold struct_T_pts_to a p x;
}

(* Flexible tails are separate element views, not evidence of an established
   whole nominal aggregate. *)
let struct_V_sizeof : SZ.t = 4sz
let struct_V_offsetof_data : SZ.t = 4sz

let struct_V_pts_to ([@@@mkey] a: ptr) (p: perm) (n: U32.t) (xs: Seq.seq U32.t) : slprop =
  uint32_t_pts_to a p n
  ** array_pts_to uint32_t_ctype uint32_t_repr 4 4 (a +! 4sz) p xs
  ** pure (U32.v n == Seq.length xs)

ghost fn uint32_t_of_elem (a: ptr) (#p: perm) (#x: U32.t)
  requires elem_pts_to uint32_t_ctype uint32_t_repr a p x
  requires pure (aligned a uint32_t_alignof)
  ensures uint32_t_pts_to a p x
{
  Pulse.Lib.C.Palow.Scalar.uint32_t_of_elem a;
}

ghost fn uint32_t_to_elem (a: ptr) (#p: perm) (#x: U32.t)
  requires uint32_t_pts_to a p x
  ensures elem_pts_to uint32_t_ctype uint32_t_repr a p x
  ensures pure (aligned a uint32_t_alignof)
{
  Pulse.Lib.C.Palow.Scalar.uint32_t_to_elem a;
}

fn struct_V_get (a: ptr) (#p: perm) (#n: erased U32.t) (#xs: Seq.seq U32.t)
                (i: SZ.t { SZ.v i < Seq.length xs })
                (off: SZ.t { SZ.v off == 4 * SZ.v i })
  requires struct_V_pts_to a p n xs
  returns r: U32.t
  ensures struct_V_pts_to a p n xs ** pure (r == Seq.index xs (SZ.v i))
{
  unfold struct_V_pts_to a p n xs;
  array_focus uint32_t_ctype uint32_t_repr (a +! 4sz) 4sz 4sz i off;
  uint32_t_of_elem ((a +! 4sz) +! off);
  let r = uint32_t_read ((a +! 4sz) +! off);
  uint32_t_to_elem ((a +! 4sz) +! off);
  array_unfocus_read uint32_t_ctype uint32_t_repr (a +! 4sz) 4sz 4sz i off;
  fold struct_V_pts_to a p n xs;
  r
}
