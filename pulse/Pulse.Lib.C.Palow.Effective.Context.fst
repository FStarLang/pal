module Pulse.Lib.C.Palow.Effective.Context

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow

module ET = Pulse.Lib.C.Palow.Etype
module Rel = Pulse.Lib.C.Palow.Effective.Relation
module R = Pulse.Lib.C.Palow.Effective.Retained
module V = Pulse.Lib.C.Palow.Effective.Value
module T = Pulse.Lib.C.Palow.Effective.Typed
module M = Pulse.Lib.C.Palow.Effective.Machine
module SZ = FStar.SizeT

(* A field keeps its enclosing context and a relational baseline. The actual
   index remains existential, but an ordinary call cannot replace its Some
   entries or introduce labels unrelated to the enclosing object. *)
let value (#t: Type) (root: ET.ctype) (lo: nat) (ct: ET.ctype)
          (repr: t -> bytes -> prop) (alignment: SZ.t)
          ([@@@mkey] a: ptr) (p: perm) (x: t) (base: ET.etypes) : slprop =
  exists* e. V.value ct repr alignment a p x e
    ** pure (Rel.retains_at base e root lo /\ Rel.view_region root lo base /\
             ET.read_ok base ct /\ Rel.strict_subobject root lo ct)

let storage (root: ET.ctype) (lo: nat) (ct: ET.ctype) (alignment: SZ.t)
            ([@@@mkey] a: ptr) (base: ET.etypes) : slprop =
  exists* e. V.storage ct alignment a e
    ** pure (Rel.retains_at base e root lo /\ Rel.view_region root lo base /\
             ET.read_ok base ct /\ Rel.strict_subobject root lo ct)

let loan (root: ET.ctype) (lo: nat) (ct: ET.ctype) ([@@@mkey] a: ptr)
         (base current: ET.etypes) : slprop =
  pure (Rel.retains_at base current root lo /\ Rel.view_region root lo base /\
        ET.read_ok base ct /\ Rel.strict_subobject root lo ct)

ghost fn claim (#t: Type0) (root: ET.ctype) (lo: nat) (ct: ET.ctype)
               (repr: t -> bytes -> prop) (alignment: SZ.t) (a: ptr)
               (#p: perm) (#x: t) (#b: bytes) (#e #base: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (repr x b /\ len b == ET.csize ct /\ ET.elen e == len b /\
                 ET.read_ok e ct /\ aligned a alignment /\
                 Rel.retains_at base e root lo /\ Rel.view_region root lo base /\
                 ET.read_ok base ct /\ Rel.strict_subobject root lo ct)
  ensures value root lo ct repr alignment a p x base
{
  V.claim ct repr alignment a #p #x #b #e;
  fold value root lo ct repr alignment a p x base;
}

ghost fn claim_storage (root: ET.ctype) (lo: nat) (ct: ET.ctype)
                       (alignment: SZ.t) (a: ptr) (#b: bytes) (#e #base: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == ET.csize ct /\ ET.elen e == len b /\
                 ET.read_ok e ct /\ aligned a alignment /\
                 Rel.retains_at base e root lo /\ Rel.view_region root lo base /\
                 ET.read_ok base ct /\ Rel.strict_subobject root lo ct)
  ensures storage root lo ct alignment a base
{
  V.claim_storage ct alignment a;
  fold storage root lo ct alignment a base;
}

let view_region_retained (base actual: ET.etypes) (root: ET.ctype) (lo: nat)
  : Lemma (requires Rel.view_region root lo base /\ Rel.retains_at base actual root lo)
          (ensures Rel.view_region root lo actual) = ()

ghost fn not_null (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                  (alignment: SZ.t) (a: ptr) (#root: ET.ctype) (#lo: nat)
                  (#p: perm) (#x: t) (#base: ET.etypes)
  preserves value root lo ct repr alignment a p x base
  ensures pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold value root lo ct repr alignment a p x base;
  V.reveal_value ct repr alignment a;
  mem_pts_to_at_not_null a;
  V.claim ct repr alignment a #p #x;
  fold value root lo ct repr alignment a p x base;
}

ghost fn reveal_value (#t: Type0) (root: ET.ctype) (lo: nat) (ct: ET.ctype)
                      (repr: t -> bytes -> prop) (alignment: SZ.t) (a: ptr)
                      (#p: perm) (#x: t) (#base: ET.etypes)
  requires value root lo ct repr alignment a p x base
  ensures exists* b e. mem_pts_to_at a p b e
    ** pure (repr x b /\ len b == ET.csize ct /\ ET.elen e == len b /\
             ET.read_ok e ct /\ aligned a alignment /\
             Rel.retains_at base e root lo /\ Rel.view_region root lo e)
{
  unfold value root lo ct repr alignment a p x base;
  with e. assert (V.value ct repr alignment a p x e);
  view_region_retained base e root lo;
  V.reveal_value ct repr alignment a;
}

ghost fn reveal_storage (root: ET.ctype) (lo: nat) (ct: ET.ctype)
                        (alignment: SZ.t) (a: ptr) (#base: ET.etypes)
  requires storage root lo ct alignment a base
  ensures exists* b e. mem_pts_to_at a 1.0R b e
    ** pure (len b == ET.csize ct /\ ET.elen e == len b /\
             ET.read_ok e ct /\ aligned a alignment /\
             Rel.retains_at base e root lo /\ Rel.view_region root lo e)
{
  unfold storage root lo ct alignment a base;
  with e. assert (V.storage ct alignment a e);
  view_region_retained base e root lo;
  V.reveal_storage ct alignment a;
}

ghost fn forget (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                (alignment: SZ.t) (a: ptr)
                (#root: ET.ctype) (#lo: nat) (#x: t) (#base: ET.etypes)
  requires value root lo ct repr alignment a 1.0R x base
  ensures storage root lo ct alignment a base
{
  unfold value root lo ct repr alignment a 1.0R x base;
  V.forget ct repr alignment a;
  fold storage root lo ct alignment a base;
}

fn read_field (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
              (alignment: SZ.t) (load: R.indexed_reader t ct repr alignment)
              (a: ptr) (#root: ET.ctype) (#lo: nat)
              (#p: perm) (#x: erased t) (#base: ET.etypes)
  preserves value root lo ct repr alignment a p x base
  returns y: t
  ensures rewrites_to y (reveal x)
{
  unfold value root lo ct repr alignment a p x base;
  let y = load a;
  fold value root lo ct repr alignment a p x base;
  y
}

fn write_uninit_field (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                      (alignment: SZ.t) (store: R.indexed_writer t ct repr alignment)
                      (a: ptr) (y: t) (#root: ET.ctype) (#lo: nat) (#base: ET.etypes)
  requires storage root lo ct alignment a base
  ensures value root lo ct repr alignment a 1.0R y base
{
  unfold storage root lo ct alignment a base;
  with e. assert (V.storage ct alignment a e);
  V.reveal_storage ct alignment a;
  V.claim_storage ct alignment a;
  R.retains_store e ct;
  Rel.retains_child_lift root lo ct e (M.store_index e ct);
  Rel.retains_at_trans base e (M.store_index e ct) root lo;
  store a y;
  fold value root lo ct repr alignment a 1.0R y base;
}

fn write_field (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
               (alignment: SZ.t) (store: R.indexed_writer t ct repr alignment)
               (a: ptr) (y: t) (#root: ET.ctype) (#lo: nat)
               (#x: erased t) (#base: ET.etypes)
  requires value root lo ct repr alignment a 1.0R x base
  ensures value root lo ct repr alignment a 1.0R y base
{
  forget ct repr alignment a;
  write_uninit_field ct repr alignment store a y;
}

ghost fn borrow_value (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                      (alignment: SZ.t) (a: ptr) (#root: ET.ctype) (#lo: nat)
                      (#p: perm) (#x: t) (#base: ET.etypes)
  requires value root lo ct repr alignment a p x base
  ensures exists* current. R.value ct repr alignment a p x current
    ** loan root lo ct a base current
{
  unfold value root lo ct repr alignment a p x base;
  with e. assert (V.value ct repr alignment a p x e);
  R.claim ct repr alignment a;
  fold loan root lo ct a base e;
}

ghost fn borrow_public_read (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                            (alignment: SZ.t) (a: ptr)
                            (#root: ET.ctype) (#lo: nat)
                            (#p: perm) (#x: t) (#base: ET.etypes)
  requires value root lo ct repr alignment a p x base
  ensures value root lo ct repr alignment a (p /. 2.0R) x base
       ** T.value ct repr alignment a (p /. 2.0R) x
{
  unfold value root lo ct repr alignment a p x base;
  with e. assert (V.value ct repr alignment a p x e);
  V.share ct repr alignment a #p #x #e;
  fold value root lo ct repr alignment a (p /. 2.0R) x base;
  fold T.value ct repr alignment a (p /. 2.0R) x;
}

ghost fn restore_public_read (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                             (alignment: SZ.t) (a: ptr)
                             (#root: ET.ctype) (#lo: nat)
                             (#p1 #p2: perm) (#x: t) (#base: ET.etypes)
  requires value root lo ct repr alignment a p1 x base
  requires T.value ct repr alignment a p2 x
  ensures value root lo ct repr alignment a (p1 +. p2) x base
{
  unfold value root lo ct repr alignment a p1 x base;
  with e1. assert (V.value ct repr alignment a p1 x e1);
  V.reveal_value ct repr alignment a #p1 #x #e1;
  with b1. assert (mem_pts_to_at a p1 b1 e1);
  T.reveal_value ct repr alignment a #p2 #x;
  with b2 e2. assert (mem_pts_to_at a p2 b2 e2);
  mem_gather_at a #p1 #p2 #b1 #b2 #e1 #e2;
  V.claim ct repr alignment a #(p1 +. p2) #x #b1 #e1;
  fold value root lo ct repr alignment a (p1 +. p2) x base;
}

ghost fn borrow_storage (ct: ET.ctype) (alignment: SZ.t) (a: ptr)
                        (#root: ET.ctype) (#lo: nat) (#base: ET.etypes)
  requires storage root lo ct alignment a base
  ensures exists* current. R.storage ct alignment a current
    ** loan root lo ct a base current
{
  unfold storage root lo ct alignment a base;
  with e. assert (V.storage ct alignment a e);
  V.reveal_storage ct alignment a;
  V.claim_storage ct alignment a;
  R.retains_refl e ct;
  fold R.storage ct alignment a e;
  fold loan root lo ct a base e;
}

ghost fn restore_value (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                       (alignment: SZ.t) (a: ptr) (#root: ET.ctype) (#lo: nat)
                       (#p: perm) (#x: t) (#base #current: ET.etypes)
  requires loan root lo ct a base current
  requires R.value ct repr alignment a p x current
  ensures value root lo ct repr alignment a p x base
{
  unfold loan root lo ct a base current;
  unfold R.value ct repr alignment a p x current;
  with e. assert (V.value ct repr alignment a p x e);
  Rel.retains_child_lift root lo ct current e;
  Rel.retains_at_trans base current e root lo;
  fold value root lo ct repr alignment a p x base;
}
