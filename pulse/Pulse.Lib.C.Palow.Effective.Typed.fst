module Pulse.Lib.C.Palow.Effective.Typed

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow

module ET = Pulse.Lib.C.Palow.Etype
module V = Pulse.Lib.C.Palow.Effective.Value
module SZ = FStar.SizeT

let repr_injective (#t: Type) (repr: t -> bytes -> prop) =
  x:t -> y:t -> b:bytes ->
    Lemma (requires repr x b /\ repr y b) (ensures x == y)

(* Existential public owners retain the very same index on reveal. The indexed
   Value interface is used when a caller must remember that index across a
   store or an aggregate decomposition. *)
let value (#t: Type) (ct: ET.ctype) (repr: t -> bytes -> prop)
          (alignment: SZ.t) ([@@@mkey] a: ptr) (p: perm) (x: t) : slprop =
  exists* e. V.value ct repr alignment a p x e

let storage (ct: ET.ctype) (alignment: SZ.t) ([@@@mkey] a: ptr) : slprop =
  exists* e. V.storage ct alignment a e

ghost fn reveal_value (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                      (alignment: SZ.t) (a: ptr) (#p: perm) (#x: t)
  requires value ct repr alignment a p x
  ensures exists* b e. mem_pts_to_at a p b e
    ** pure (repr x b /\ len b == ET.csize ct /\ ET.elen e == len b /\
             ET.read_ok e ct /\ aligned a alignment)
{
  unfold value ct repr alignment a p x;
  with e. assert (V.value ct repr alignment a p x e);
  V.reveal_value ct repr alignment a;
}

ghost fn claim (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
               (alignment: SZ.t) (a: ptr) (#p: perm) (#x: t)
               (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (repr x b /\ len b == ET.csize ct /\ ET.elen e == len b /\
                 ET.read_ok e ct /\ aligned a alignment)
  ensures value ct repr alignment a p x
{
  V.claim ct repr alignment a #p #x #b #e;
  fold value ct repr alignment a p x;
}

ghost fn reveal_storage (ct: ET.ctype) (alignment: SZ.t) (a: ptr)
  requires storage ct alignment a
  ensures exists* b e. mem_pts_to_at a 1.0R b e
    ** pure (len b == ET.csize ct /\ ET.elen e == len b /\
             ET.read_ok e ct /\ aligned a alignment)
{
  unfold storage ct alignment a;
  with e. assert (V.storage ct alignment a e);
  unfold V.storage ct alignment a e;
}

ghost fn claim_storage (ct: ET.ctype) (alignment: SZ.t) (a: ptr)
                       (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == ET.csize ct /\ ET.elen e == len b /\
                 ET.read_ok e ct /\ aligned a alignment)
  ensures storage ct alignment a
{
  fold V.storage ct alignment a e;
  fold storage ct alignment a;
}

ghost fn forget (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                (alignment: SZ.t) (a: ptr) (#x: t)
  requires value ct repr alignment a 1.0R x
  ensures storage ct alignment a
{
  unfold value ct repr alignment a 1.0R x;
  with e. assert (V.value ct repr alignment a 1.0R x e);
  V.forget ct repr alignment a;
  fold storage ct alignment a;
}

ghost fn share (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
               (alignment: SZ.t) (a: ptr) (#p: perm) (#x: t)
  requires value ct repr alignment a p x
  ensures value ct repr alignment a (p /. 2.0R) x
       ** value ct repr alignment a (p /. 2.0R) x
{
  unfold value ct repr alignment a p x;
  with e. assert (V.value ct repr alignment a p x e);
  V.share ct repr alignment a;
  fold value ct repr alignment a (p /. 2.0R) x;
  fold value ct repr alignment a (p /. 2.0R) x;
}

fn write (#t: Type0) (ct: erased ET.ctype) (repr: t -> bytes -> prop)
         (alignment: SZ.t) (a: ptr) (x: t) (b: bytes)
  requires storage (reveal ct) alignment a
  requires pure (repr x b /\ len b == ET.csize (reveal ct) /\ initialized b)
  ensures value (reveal ct) repr alignment a 1.0R x
{
  reveal_storage (reveal ct) alignment a;
  with old e. assert (mem_pts_to_at a 1.0R old e);
  fold V.storage (reveal ct) alignment a e;
  V.write ct repr alignment a x b;
  fold value (reveal ct) repr alignment a 1.0R x;
}

ghost fn not_null (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                  (alignment: SZ.t) (a: ptr) (#p: perm) (#x: t)
  preserves value ct repr alignment a p x
  requires pure (ET.csize ct > 0)
  ensures pure (not (is_null a) /\ Some? (prov_of a))
{
  reveal_value ct repr alignment a;
  with b e. assert (mem_pts_to_at a p b e);
  mem_pts_to_at_not_null a;
  claim ct repr alignment a #p #x #b #e;
}

ghost fn storage_not_null (ct: ET.ctype) (alignment: SZ.t) (a: ptr)
  preserves storage ct alignment a
  requires pure (ET.csize ct > 0)
  ensures pure (not (is_null a) /\ Some? (prov_of a))
{
  reveal_storage ct alignment a;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  mem_pts_to_at_not_null a;
  claim_storage ct alignment a;
}

[@@allow_ambiguous]
ghost fn agree (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
               (alignment: SZ.t)
               (injective: repr_injective repr)
               (a: ptr) (#p1 #p2: perm) (#x #y: t)
  preserves value ct repr alignment a p1 x
  preserves value ct repr alignment a p2 y
  ensures pure (x == y)
{
  reveal_value ct repr alignment a #p1 #x;
  with b1 e1. assert (mem_pts_to_at a p1 b1 e1);
  reveal_value ct repr alignment a #p2 #y;
  with b2 e2. assert (mem_pts_to_at a p2 b2 e2);
  mem_pts_to_at_bytes_injective a;
  injective x y b1;
  claim ct repr alignment a #p1 #x #b1 #e1;
  claim ct repr alignment a #p2 #y #b2 #e2;
}

[@@allow_ambiguous]
ghost fn gather (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                (alignment: SZ.t)
                (injective: repr_injective repr)
                (a: ptr) (#p1 #p2: perm) (#x #y: t)
  requires value ct repr alignment a p1 x
  requires value ct repr alignment a p2 y
  ensures value ct repr alignment a (p1 +. p2) x ** pure (x == y)
{
  reveal_value ct repr alignment a #p1 #x;
  with b1 e1. assert (mem_pts_to_at a p1 b1 e1);
  reveal_value ct repr alignment a #p2 #y;
  with b2 e2. assert (mem_pts_to_at a p2 b2 e2);
  mem_gather_at a;
  injective x y b1;
  claim ct repr alignment a #(p1 +. p2) #x #b1 #e1;
}
