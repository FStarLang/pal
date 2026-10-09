module Pulse.Lib.C.Palow.Index

(* ---------------------------------------------------------------------------
   Moving between the indexed and unindexed byte views.

   `Pulse.Lib.C.Palow` states the relationship between `mem_pts_to_at` and
   `mem_pts_to` as an slprop *equality*, for the reason given there: a pair of
   axiomatized ghost steps between two independent predicates could be used to
   discard an effective-type index and conjure a fresh one, and an equality
   cannot.

   Using an equality in a Pulse proof means a `rewrite`, and the two rewrites
   involved are the same two every time. They are packaged here, *derived* from
   the equality rather than assumed -- this module has an implementation, and
   adds no axioms.

   The asymmetry between them is the point of the whole design. `hide` forgets
   which index the bytes carry; `show` gets *an* index back, but only as an
   existential, so nothing can be concluded about it. Going round the loop
   therefore loses information and never gains any: bytes that came out of a
   declared `int` cannot be put back as a `float`, because re-establishing a
   typed points-to needs `read_ok` of the index it actually has, and after a
   `hide` nobody can prove that about anything.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow

module ET = Pulse.Lib.C.Palow.Etype
module SZ = FStar.SizeT

(* Forget the index. This is what a typed `reveal` does for callers that only
   want the bytes -- `memcpy`, padding, the split and join machinery -- and it
   is why those are unaffected by effective types. *)
ghost fn mem_hide_etypes (a: ptr) (#p: perm) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (ET.elen e == len b /\ ET.allocated e)
  ensures  mem_pts_to a p b

(* Recover the index. The result is existential, so this does not let a caller
   choose one: combined with `mem_pts_to_at_injective` it names the index the
   bytes already had, and nothing more. *)
ghost fn mem_show_etypes (a: ptr) (#p: perm) (#b: bytes)
  requires mem_pts_to a p b
  ensures  exists* e. mem_pts_to_at a p b e
             ** pure (ET.elen e == len b /\ ET.allocated e)

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

(* ---------------------------------------------------------------------------
   Observing an indexed range

   Layer 0 states nullness and bounds over `mem_pts_to`, because neither has
   anything to do with effective types. A typed points-to that carries an
   index cannot use them directly, though: the facts are stated with
   `preserves`, and reaching them through `hide` and `show` would hand back a
   range whose index is existential -- which is exactly the information the
   typed predicate needs to keep.

   So each is restated here over `mem_pts_to_at` and *derived*: share the
   range, observe through one half, gather the halves back. Gathering is what
   recovers the index, since `mem_gather_at` returns the index of the half
   that was never rewritten.

   Only the facts that survive halving the permission are here. A fact about
   the permission itself (`mem_pts_to_perm_bound`) does not -- observing
   through a half shows `p /. 2.0R <=. 1.0R`, which is weaker than wanted --
   and neither does one needing the whole of a range (`mem_pts_to_disjoint`,
   which needs `1.0R` and so leaves nothing to retain the index with). Both
   are omitted rather than assumed: nothing needs them yet, and when something
   does, the honest response is a layer-0 axiom, as with `mem_share_at`.
   --------------------------------------------------------------------------- *)

ghost fn mem_pts_to_at_not_null (a: ptr) (#p: perm) (#b: bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires  pure (ET.elen e == len b /\ ET.allocated e /\ len b > 0)
  ensures   pure (not (is_null a) /\ Some? (prov_of a))

ghost fn mem_pts_to_at_fits (a: ptr) (#p: perm) (#b: bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires  pure (ET.elen e == len b /\ ET.allocated e)
  ensures   pure (SZ.fits (addr_of a + len b))
