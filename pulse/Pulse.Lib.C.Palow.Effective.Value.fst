module Pulse.Lib.C.Palow.Effective.Value

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow

module ET = Pulse.Lib.C.Palow.Etype
module E = Pulse.Lib.C.Palow.Effective
module M = Pulse.Lib.C.Palow.Effective.Machine
module Seq = FStar.Seq
module SZ = FStar.SizeT

(* The index stays explicit through all representation conversions. Forgetting
   a value loses initialization knowledge, not its type or storage origin. *)
let value (#t: Type) (ct: ET.ctype) (repr: t -> bytes -> prop) (alignment: SZ.t)
          ([@@@mkey] a: ptr) (p: perm) (x: t) (e: ET.etypes) : slprop =
  exists* b. mem_pts_to_at a p b e
    ** pure (repr x b /\ len b == ET.csize ct /\ ET.elen e == len b /\
             ET.read_ok e ct /\ aligned a alignment)

let storage (ct: ET.ctype) (alignment: SZ.t) ([@@@mkey] a: ptr) (e: ET.etypes)
  : slprop =
  exists* b. mem_pts_to_at a 1.0R b e
    ** pure (len b == ET.csize ct /\ ET.elen e == len b /\
             ET.read_ok e ct /\ aligned a alignment)

ghost fn claim (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
               (alignment: SZ.t) (a: ptr) (#p: perm) (#x: t)
               (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (repr x b /\ len b == ET.csize ct /\ ET.elen e == len b /\
                 ET.read_ok e ct /\ aligned a alignment)
  ensures value ct repr alignment a p x e
{
  fold value ct repr alignment a p x e;
}

ghost fn reveal_value (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                (alignment: SZ.t) (a: ptr) (#p: perm) (#x: t) (#e: ET.etypes)
  requires value ct repr alignment a p x e
  ensures exists* b. mem_pts_to_at a p b e
    ** pure (repr x b /\ len b == ET.csize ct /\ ET.elen e == len b /\
             ET.read_ok e ct /\ aligned a alignment)
{
  unfold value ct repr alignment a p x e;
}

ghost fn forget (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
                (alignment: SZ.t) (a: ptr) (#x: t) (#e: ET.etypes)
  requires value ct repr alignment a 1.0R x e
  ensures storage ct alignment a e
{
  unfold value ct repr alignment a 1.0R x e;
  fold storage ct alignment a e;
}

[@@allow_ambiguous]
ghost fn share (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
               (alignment: SZ.t) (a: ptr) (#p: perm) (#x: t) (#e: ET.etypes)
  requires value ct repr alignment a p x e
  ensures value ct repr alignment a (p /. 2.0R) x e
       ** value ct repr alignment a (p /. 2.0R) x e
{
  unfold value ct repr alignment a p x e;
  mem_share_at a;
  fold value ct repr alignment a (p /. 2.0R) x e;
  fold value ct repr alignment a (p /. 2.0R) x e;
}

fn write (#t: Type0) (ct: erased ET.ctype) (repr: t -> bytes -> prop)
         (alignment: SZ.t) (a: ptr) (x: t) (b: bytes)
         (#e: ET.etypes { ET.elen e == ET.csize (reveal ct) })
  requires storage (reveal ct) alignment a e
  requires pure (repr x b /\ len b == ET.csize (reveal ct) /\ initialized b)
  ensures value (reveal ct) repr alignment a 1.0R x (M.store_index e (reveal ct))
{
  unfold storage (reveal ct) alignment a e;
  M.store a ct b;
  ET.store_read_ok e (reveal ct);
  fold value (reveal ct) repr alignment a 1.0R x (M.store_index e (reveal ct));
}

fn initialize (#t: Type0) (ct: erased ET.ctype) (repr: t -> bytes -> prop)
              (alignment: SZ.t) (a: ptr) (x: t) (b: bytes)
  requires E.prepared a (reveal ct)
  requires pure (repr x b /\ len b == ET.csize (reveal ct) /\
                 initialized b /\ aligned a alignment)
  ensures exists* e. value (reveal ct) repr alignment a 1.0R x e
    ** pure (E.mutable_index e /\
             (not (ET.character_type (reveal ct)) ==>
               e == ET.etypes_of (reveal ct) false))
{
  M.initialize a ct b;
  with e. assert (mem_pts_to_at a 1.0R b e);
  fold value (reveal ct) repr alignment a 1.0R x e;
}

(* This works for aggregate members, array elements, and character views.
   The enclosing labels and offsets are retained, never replaced by a field's
   nominal type. The caller splits and rejoins them with indexed byte laws. *)
ghost fn claim_component (#t: Type0) (parent child: ET.ctype)
                         (repr: t -> bytes -> prop) (alignment: SZ.t) (a: ptr)
                         (#p: perm) (#x: t) (#b: bytes) (#e: ET.etypes)
                         (off: nat { off + ET.csize child <= ET.elen e })
  requires mem_pts_to_at a p b (Seq.slice e off (off + ET.csize child))
  requires pure (ET.read_ok e parent /\ ET.access_ok parent off child /\ ET.compose_ok parent child /\
                 repr x b /\ len b == ET.csize child /\ aligned a alignment)
  ensures value child repr alignment a p x
            (Seq.slice e off (off + ET.csize child))
{
  ET.read_ok_slice e parent off child;
  fold value child repr alignment a p x (Seq.slice e off (off + ET.csize child));
}

ghost fn reveal_storage (ct: ET.ctype) (alignment: SZ.t) (a: ptr)
                        (#e: ET.etypes)
  requires storage ct alignment a e
  ensures exists* b. mem_pts_to_at a 1.0R b e
    ** pure (len b == ET.csize ct /\ ET.elen e == len b /\
             ET.read_ok e ct /\ aligned a alignment)
{
  unfold storage ct alignment a e;
}

ghost fn claim_storage (ct: ET.ctype) (alignment: SZ.t) (a: ptr)
                       (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == ET.csize ct /\ ET.elen e == len b /\
                 ET.read_ok e ct /\ aligned a alignment)
  ensures storage ct alignment a e
{
  fold storage ct alignment a e;
}

(* A reservation requires the actual complete old index, not just an
   allocation token or a nominal type remembered by a caller. *)
ghost fn prepare_storage (old: ET.ctype) (alignment: SZ.t) (a: ptr)
                         (target: ET.ctype) (#e: ET.etypes)
  requires storage old alignment a e
  requires pure (ET.full_mutable e /\ ET.elen e == ET.csize target)
  ensures E.prepared a target
{
  unfold storage old alignment a e;
  E.prepare a target;
}

fn write_existing (#t: Type0) (ct: erased ET.ctype) (repr: t -> bytes -> prop)
                  (alignment: SZ.t) (a: ptr) (x: t) (b: bytes)
                  (#e: ET.etypes { ET.elen e == ET.csize (reveal ct) })
  requires storage (reveal ct) alignment a e
  requires pure (repr x b /\ len b == ET.csize (reveal ct) /\ initialized b /\
    (forall (k: nat). k < ET.elen e ==> Some? (ET.eget e k)))
  ensures value (reveal ct) repr alignment a 1.0R x e
{
  unfold storage (reveal ct) alignment a e;
  ET.store_readable_stable e (reveal ct);
  M.store a ct b;
  fold value (reveal ct) repr alignment a 1.0R x e;
}
