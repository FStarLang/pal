module Pulse.Lib.C.Palow.Effective

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow

module ET = Pulse.Lib.C.Palow.Etype
module Alloc = Pulse.Lib.C.Palow.Alloc
module SZ = FStar.SizeT

let prepared ([@@@mkey] a: ptr) (t: ET.ctype) : slprop =
  exists* b e. mem_pts_to_at a 1.0R b e
    ** pure (len b == ET.csize t /\ ET.elen e == len b /\ mutable_index e)

ghost fn prepare (a: ptr) (t: ET.ctype) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == ET.csize t /\ ET.elen e == len b /\ ET.full_mutable e)
  ensures prepared a t
{
  fold prepared a t;
}

ghost fn prepare_allocation (a: ptr) (n: SZ.t) (t: ET.ctype)
                            (#b: bytes) (#e: ET.etypes)
  preserves Alloc.freeable a n
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v n /\ SZ.v n == ET.csize t /\ ET.elen e == len b /\
                 ET.full_mutable e)
  ensures prepared a t
{
  prepare a t;
}

let readable ([@@@mkey] a: ptr) (p: perm) (b: bytes) (t: ET.ctype) : slprop =
  exists* e. mem_pts_to_at a p b e
    ** pure (ET.read_ok e t /\ ET.elen e == len b)

ghost fn conceal (a: ptr) (t: ET.ctype) (#p: perm) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (ET.read_ok e t /\ ET.elen e == len b)
  ensures readable a p b t
{
  fold readable a p b t;
}

ghost fn reveal (a: ptr) (t: ET.ctype) (#p: perm) (#b: bytes)
  requires readable a p b t
  ensures exists* e. mem_pts_to_at a p b e
                     ** pure (ET.read_ok e t /\ ET.elen e == len b)
{
  unfold readable a p b t;
}

[@@allow_ambiguous]
ghost fn share (a: ptr) (t: ET.ctype) (#p: perm) (#b: bytes)
  requires readable a p b t
  ensures readable a (p /. 2.0R) b t ** readable a (p /. 2.0R) b t
{
  unfold readable a p b t;
  with e. assert (mem_pts_to_at a p b e);
  mem_share_at a;
  fold readable a (p /. 2.0R) b t;
  fold readable a (p /. 2.0R) b t;
}
