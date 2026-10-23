module Pulse.Lib.C.Palow.Effective

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow

module ET = Pulse.Lib.C.Palow.Etype
module Alloc = Pulse.Lib.C.Palow.Alloc
module SZ = FStar.SizeT

let mutable_index (e: ET.etypes) : prop =
  ET.all_mutable e

(* Unlike ordinary value-forgetting, preparation hides the bytes themselves.
   Only a machine initialization can produce readable ownership again. *)
val prepared ([@@@mkey] a: ptr) (t: ET.ctype) : slprop

ghost fn prepare (a: ptr) (t: ET.ctype) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == ET.csize t /\ ET.elen e == len b /\ ET.full_mutable e)
  ensures prepared a t

(* The allocation wrapper preserves deallocation eligibility, but does not
   infer metadata origin or uniformity from the free token. *)
ghost fn prepare_allocation (a: ptr) (n: SZ.t) (t: ET.ctype)
                            (#b: bytes) (#e: ET.etypes)
  preserves Alloc.freeable a n
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v n /\ SZ.v n == ET.csize t /\ ET.elen e == len b /\
                 ET.full_mutable e)
  ensures prepared a t

(* The immutable allocation certificate establishes only origin. Reserving the
   entire allocation hides its previous, potentially heterogeneous, index. *)
ghost fn prepare_allocated (a: ptr) (n: SZ.t) (t: ET.ctype)
                           (#b: bytes) (#e: ET.etypes)
  preserves Alloc.freeable a n
  requires mem_pts_to_at a 1.0R b e
  requires pure (allocated_region a (SZ.v n) /\ len b == SZ.v n /\
                 SZ.v n == ET.csize t /\ ET.elen e == len b)
  ensures prepared a t

ghost fn prepare_region (a: ptr) (t: ET.ctype) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (allocated_region a (ET.csize t) /\ len b == ET.csize t /\
                 ET.elen e == len b)
  ensures prepared a t

(* This is an access view, not a replacement effective type. *)
val readable ([@@@mkey] a: ptr) (p: perm) (b: bytes) (t: ET.ctype) : slprop

ghost fn conceal (a: ptr) (t: ET.ctype) (#p: perm) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (ET.read_ok e t /\ ET.elen e == len b)
  ensures readable a p b t

ghost fn reveal (a: ptr) (t: ET.ctype) (#p: perm) (#b: bytes)
  requires readable a p b t
  ensures exists* e. mem_pts_to_at a p b e
                     ** pure (ET.read_ok e t /\ ET.elen e == len b)

[@@allow_ambiguous]
ghost fn share (a: ptr) (t: ET.ctype) (#p: perm) (#b: bytes)
  requires readable a p b t
  ensures readable a (p /. 2.0R) b t ** readable a (p /. 2.0R) b t
