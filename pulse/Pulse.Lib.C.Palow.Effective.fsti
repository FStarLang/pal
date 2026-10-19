module Pulse.Lib.C.Palow.Effective

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow

module ET = Pulse.Lib.C.Palow.Etype

let mutable_index (e: ET.etypes) : prop =
  ET.full_mutable e

(* Unlike ordinary value-forgetting, preparation hides the bytes themselves.
   Only a machine initialization can produce readable ownership again. *)
val prepared ([@@@mkey] a: ptr) (t: ET.ctype) : slprop

ghost fn prepare (a: ptr) (t: ET.ctype) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == ET.csize t /\ ET.elen e == len b /\ mutable_index e)
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
