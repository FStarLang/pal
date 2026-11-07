module Pulse.Lib.C.Palow.Effective.Retained

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow

module ET = Pulse.Lib.C.Palow.Etype
module V = Pulse.Lib.C.Palow.Effective.Value
module T = Pulse.Lib.C.Palow.Effective.Typed
module M = Pulse.Lib.C.Palow.Effective.Machine
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Relation = Pulse.Lib.C.Palow.Effective.Relation

type indexed_reader (t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                    (alignment: SZ.t) =
  a:ptr -> #p:perm -> #x:erased t -> #e:ET.etypes ->
  stt t (V.value ct repr alignment a p x e)
    (fun y -> V.value ct repr alignment a p x e ** pure (y == reveal x))

type indexed_writer (t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                    (alignment: SZ.t) =
  a:ptr -> y:t -> #e:ET.etypes { ET.elen e == ET.csize ct } ->
  stt unit (V.storage ct alignment a e)
    (fun _ -> V.value ct repr alignment a 1.0R y (M.store_index e ct))

type repr_sized (t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop) =
  x:t -> b:bytes -> Lemma (requires repr x b) (ensures len b == ET.csize ct)

type public_revealer (t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                     (alignment: SZ.t) (owned: ptr -> perm -> t -> slprop) =
  a:ptr -> #p:perm -> #x:t ->
  stt_ghost unit emp_inames (owned a p x)
    (fun _ -> exists* b e. mem_pts_to_at a p b e
      ** pure (ET.elen e == len b /\ ET.read_ok e ct /\ repr x b /\ aligned a alignment))

type public_concealer (t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                      (alignment: SZ.t) (owned: ptr -> perm -> t -> slprop) =
  a:ptr -> #p:perm -> #b:bytes -> #x:t -> #e:ET.etypes ->
  stt_ghost unit emp_inames
    (mem_pts_to_at a p b e ** pure (repr x b) ** pure (aligned a alignment)
      ** pure (ET.elen e == len b /\ ET.read_ok e ct))
    (fun _ -> owned a p x)

(* Ordinary calls may establish compatible subobjects in previously untyped
   bytes, but cannot replace an already established enclosing type or origin. *)
let retains (base current: ET.etypes) (ct: ET.ctype) : prop =
  Relation.retains base current ct

let retains_refl (e: ET.etypes) (ct: ET.ctype { ET.elen e == ET.csize ct })
  : Lemma (retains e e ct) = Relation.retains_refl e ct

let retains_trans (base middle current: ET.etypes) (ct: ET.ctype)
  : Lemma (requires retains base middle ct /\ retains middle current ct)
          (ensures retains base current ct) = Relation.retains_trans base middle current ct

let retains_store (e: ET.etypes) (ct: ET.ctype { ET.elen e == ET.csize ct })
  : Lemma (requires ET.read_ok e ct)
          (ensures retains e (M.store_index e ct) ct)
  = if ET.character_type ct then Relation.retains_refl e ct
    else Relation.retains_store e ct

let value (#t: Type) (ct: ET.ctype) (repr: t -> bytes -> prop) (alignment: SZ.t)
          ([@@@mkey] a: ptr) (p: perm) (x: t) (base: ET.etypes) : slprop =
  exists* e. V.value ct repr alignment a p x e ** pure (retains base e ct)

let pts_to (#t: Type) (ct: ET.ctype) (repr: t -> bytes -> prop) (alignment: SZ.t)
           (base: ET.etypes) ([@@@mkey] a: ptr) (p: perm) (x: t) : slprop =
  value ct repr alignment a p x base

let storage (ct: ET.ctype) (alignment: SZ.t) ([@@@mkey] a: ptr)
            (base: ET.etypes) : slprop =
  exists* e. V.storage ct alignment a e ** pure (retains base e ct)

ghost fn retain (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                (alignment: SZ.t) (a: ptr) (#p: perm) (#x: t)
  requires T.value ct repr alignment a p x
  ensures exists* base. value ct repr alignment a p x base
{
  unfold T.value ct repr alignment a p x;
  with e. assert (V.value ct repr alignment a p x e);
  V.reveal_value ct repr alignment a;
  with b. assert (mem_pts_to_at a p b e);
  V.claim ct repr alignment a #p #x #b #e;
  retains_refl e ct;
  fold value ct repr alignment a p x e;
}

ghost fn release (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                 (alignment: SZ.t) (a: ptr) (#p: perm) (#x: t) (#base: ET.etypes)
  requires value ct repr alignment a p x base
  ensures T.value ct repr alignment a p x
{
  unfold value ct repr alignment a p x base;
  fold T.value ct repr alignment a p x;
}

ghost fn retain_storage (ct: ET.ctype) (alignment: SZ.t) (a: ptr)
  requires T.storage ct alignment a
  ensures exists* base. storage ct alignment a base
{
  unfold T.storage ct alignment a;
  with e. assert (V.storage ct alignment a e);
  V.reveal_storage ct alignment a;
  V.claim_storage ct alignment a;
  retains_refl e ct;
  fold storage ct alignment a e;
}

ghost fn claim (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
               (alignment: SZ.t) (a: ptr) (#p: perm) (#x: t) (#e: ET.etypes)
  requires V.value ct repr alignment a p x e
  ensures value ct repr alignment a p x e
{
  V.reveal_value ct repr alignment a;
  with b. assert (mem_pts_to_at a p b e);
  V.claim ct repr alignment a #p #x #b #e;
  retains_refl e ct;
  fold value ct repr alignment a p x e;
}

ghost fn claim_raw (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                   (alignment: SZ.t) (a: ptr) (#p: perm) (#x: t)
                   (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (repr x b /\ len b == ET.csize ct /\ ET.elen e == len b /\
                 ET.read_ok e ct /\ aligned a alignment)
  ensures value ct repr alignment a p x e
{
  V.claim ct repr alignment a #p #x #b #e;
  claim ct repr alignment a #p #x #e;
}

ghost fn claim_storage_raw (ct: ET.ctype) (alignment: SZ.t) (a: ptr)
                           (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == ET.csize ct /\ ET.elen e == len b /\
                 ET.read_ok e ct /\ aligned a alignment)
  ensures storage ct alignment a e
{
  V.claim_storage ct alignment a;
  retains_refl e ct;
  fold storage ct alignment a e;
}

ghost fn reveal_value (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                      (alignment: SZ.t) (a: ptr) (#p: perm) (#x: t)
                      (#base: ET.etypes)
  requires value ct repr alignment a p x base
  ensures exists* b e. mem_pts_to_at a p b e
    ** pure (repr x b /\ len b == ET.csize ct /\ ET.elen e == len b /\
             ET.read_ok e ct /\ aligned a alignment /\ retains base e ct)
{
  unfold value ct repr alignment a p x base;
  V.reveal_value ct repr alignment a;
}

ghost fn retain_opaque (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                       (alignment: SZ.t) (repr_len: repr_sized t ct repr)
                       (owned: ptr -> perm -> t -> slprop)
                       (expose: public_revealer t ct repr alignment owned)
                       (a: ptr) (#p: perm) (#x: t)
  requires owned a p x
  ensures exists* base. value ct repr alignment a p x base
{
  expose a #p #x;
  with b e. assert (mem_pts_to_at a p b e);
  repr_len x b;
  claim_raw ct repr alignment a #p #x #b #e;
}

ghost fn release_opaque (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                        (alignment: SZ.t) (owned: ptr -> perm -> t -> slprop)
                        (conceal_owner: public_concealer t ct repr alignment owned)
                        (a: ptr) (#p: perm) (#x: t) (#base: ET.etypes)
  requires value ct repr alignment a p x base
  ensures owned a p x
{
  reveal_value ct repr alignment a;
  with b e. assert (mem_pts_to_at a p b e);
  conceal_owner a #p #b #x #e;
}

ghost fn conceal (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                 (alignment: SZ.t) (a: ptr) (#p: perm) (#x: t)
                 (#e #base: ET.etypes)
  requires V.value ct repr alignment a p x e
  requires pure (retains base e ct)
  ensures value ct repr alignment a p x base
{
  fold value ct repr alignment a p x base;
}

(* The retained fraction pins the actual bytes and index while the public
   fraction crosses a read-only interface that hides its index. *)
ghost fn borrow_public_read (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                            (alignment: SZ.t) (a: ptr)
                            (#p: perm) (#x: t) (#base: ET.etypes)
  requires value ct repr alignment a p x base
  ensures value ct repr alignment a (p /. 2.0R) x base
       ** T.value ct repr alignment a (p /. 2.0R) x
{
  unfold value ct repr alignment a p x base;
  with e. assert (V.value ct repr alignment a p x e);
  V.share ct repr alignment a #p #x #e;
  fold value ct repr alignment a (p /. 2.0R) x base;
  fold T.value ct repr alignment a (p /. 2.0R) x;
}

ghost fn restore_public_read (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                             (alignment: SZ.t) (a: ptr)
                             (#p1 #p2: perm) (#x: t) (#base: ET.etypes)
  requires value ct repr alignment a p1 x base
  requires T.value ct repr alignment a p2 x
  ensures value ct repr alignment a (p1 +. p2) x base
{
  reveal_value ct repr alignment a #p1 #x #base;
  with b1 e1. assert (mem_pts_to_at a p1 b1 e1);
  T.reveal_value ct repr alignment a #p2 #x;
  with b2 e2. assert (mem_pts_to_at a p2 b2 e2);
  mem_gather_at a #p1 #p2 #b1 #b2 #e1 #e2;
  V.claim ct repr alignment a #(p1 +. p2) #x #b1 #e1;
  conceal ct repr alignment a #(p1 +. p2) #x #e1 #base;
}

ghost fn forget (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                (alignment: SZ.t) (a: ptr) (#x: t) (#base: ET.etypes)
  requires value ct repr alignment a 1.0R x base
  ensures storage ct alignment a base
{
  unfold value ct repr alignment a 1.0R x base;
  V.forget ct repr alignment a;
  fold storage ct alignment a base;
}

ghost fn reveal_storage (ct: ET.ctype) (alignment: SZ.t) (a: ptr)
                        (#base: ET.etypes)
  requires storage ct alignment a base
  ensures exists* b e. mem_pts_to_at a 1.0R b e
    ** pure (len b == ET.csize ct /\ ET.elen e == len b /\
             ET.read_ok e ct /\ aligned a alignment /\ retains base e ct)
{
  unfold storage ct alignment a base;
  V.reveal_storage ct alignment a;
}

ghost fn open_write (ct: ET.ctype) (alignment: SZ.t) (a: ptr)
                    (#base: ET.etypes)
  requires storage ct alignment a base
  ensures exists* (e: ET.etypes { ET.elen e == ET.csize ct }).
    V.storage ct alignment a e ** pure (retains base (M.store_index e ct) ct)
{
  unfold storage ct alignment a base;
  with e. assert (V.storage ct alignment a e);
  V.reveal_storage ct alignment a;
  retains_store e ct;
  retains_trans base e (M.store_index e ct) ct;
  V.claim_storage ct alignment a;
}

fn read_retained (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                 (alignment: SZ.t) (load: indexed_reader t ct repr alignment)
                 (a: ptr) (#p: perm) (#x: erased t) (#base: ET.etypes)
  preserves value ct repr alignment a p x base
  returns y: t
  ensures rewrites_to y (reveal x)
{
  unfold value ct repr alignment a p x base;
  let y = load a;
  fold value ct repr alignment a p x base;
  y
}

fn write_uninit_retained (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                         (alignment: SZ.t) (store: indexed_writer t ct repr alignment)
                         (a: ptr) (y: t) (#base: ET.etypes)
  requires storage ct alignment a base
  ensures value ct repr alignment a 1.0R y base
{
  open_write ct alignment a;
  store a y;
  fold value ct repr alignment a 1.0R y base;
}

fn write_retained (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                  (alignment: SZ.t) (store: indexed_writer t ct repr alignment)
                  (a: ptr) (y: t) (#x: erased t) (#base: ET.etypes)
  requires value ct repr alignment a 1.0R x base
  ensures value ct repr alignment a 1.0R y base
{
  forget ct repr alignment a;
  write_uninit_retained ct repr alignment store a y;
}

fn write (#t: Type0) (ct: erased ET.ctype) (repr: t -> bytes -> prop)
         (alignment: SZ.t) (a: ptr) (x: t) (b: bytes) (#base: ET.etypes)
  requires storage (reveal ct) alignment a base
  requires pure (repr x b /\ len b == ET.csize (reveal ct) /\ initialized b)
  ensures value (reveal ct) repr alignment a 1.0R x base
{
  unfold storage (reveal ct) alignment a base;
  with e. assert (V.storage (reveal ct) alignment a e);
  V.reveal_storage (reveal ct) alignment a;
  with old. assert (mem_pts_to_at a 1.0R old e);
  V.claim_storage (reveal ct) alignment a;
  retains_store e (reveal ct);
  V.write ct repr alignment a x b;
  retains_trans base e (M.store_index e (reveal ct)) (reveal ct);
  fold value (reveal ct) repr alignment a 1.0R x base;
}
