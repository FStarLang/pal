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

(* Giving allocated storage a new effective type. This is 6.5p6 for the case
   the generated code cannot reach on its own: a store through an lvalue of
   type `c` sets the stored-into object's effective type to `c`, and an
   allocator that hands out raw storage has to be able to take that step for a
   chunk it pre-filled. It is available precisely because the storage is
   `allocated` -- no byte of it is at a declared type -- which is what
   `allocated_store_ok` says, and it is unavailable for a declared object,
   which is what C says too. *)
ghost fn mem_retype (a: ptr) (c: ET.ctype) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (ET.elen e == len b /\ len b == ET.csize c /\ ET.allocated e
                 /\ ~(c == ET.tchar))
  ensures  exists* e'. mem_pts_to_at a 1.0R b e'
             ** pure (ET.elen e' == len b /\ ET.read_ok e' c /\ ET.allocated e')
{
  ET.allocated_store_ok e c;
  mem_store_etypes a c;
  ET.store_ok_read_ok e c;
  ET.allocated_store_etypes e c;
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
