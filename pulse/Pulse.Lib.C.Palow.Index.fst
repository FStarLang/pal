module Pulse.Lib.C.Palow.Index

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow

module ET = Pulse.Lib.C.Palow.Etype
module SZ = FStar.SizeT

ghost fn mem_hide_etypes (a: ptr) (#p: perm) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (ET.elen e == len b /\ ET.allocated e)
  ensures  mem_pts_to a p b
{
  mem_pts_to_at_eq a p b;
  rewrite (exists* e. mem_pts_to_at a p b e ** pure (ET.elen e == len b /\ ET.allocated e))
       as (mem_pts_to a p b);
}

ghost fn mem_show_etypes (a: ptr) (#p: perm) (#b: bytes)
  requires mem_pts_to a p b
  ensures  exists* e. mem_pts_to_at a p b e
             ** pure (ET.elen e == len b /\ ET.allocated e)
{
  mem_pts_to_at_eq a p b;
  rewrite (mem_pts_to a p b)
       as (exists* e. mem_pts_to_at a p b e ** pure (ET.elen e == len b /\ ET.allocated e));
}

(* The share/observe/gather dance, five times. Each one spends half the range
   on a rewrite to the unindexed view, which is what makes the layer-0 fact
   applicable, and recovers the index from the half that stayed behind. *)

ghost fn mem_pts_to_at_not_null (a: ptr) (#p: perm) (#b: bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires  pure (ET.elen e == len b /\ ET.allocated e /\ len b > 0)
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  mem_share_at a;
  mem_hide_etypes a;
  mem_pts_to_not_null a;
  mem_show_etypes a;
  mem_gather_at a;
}

ghost fn mem_pts_to_at_fits (a: ptr) (#p: perm) (#b: bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires  pure (ET.elen e == len b /\ ET.allocated e)
  ensures   pure (SZ.fits (addr_of a + len b))
{
  mem_share_at a;
  mem_hide_etypes a;
  mem_pts_to_fits a;
  mem_show_etypes a;
  mem_gather_at a;
}
