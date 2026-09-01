module Pulse.Lib.C.Palow

(* ---------------------------------------------------------------------------
   Palow layer 0: byte-level ownership.

   `mem_pts_to a p b` is fractional ownership, at permission `p`, of the
   `len b` bytes starting at `a`, whose current contents are `b`. Everything
   else in Palow is defined on top of this: a typed points-to for a C type `t`
   is

     let t_pts_to a p x = exists* b. mem_pts_to a p b ** pure (t_repr x b)

   so ordinary generated code never mentions `mem_pts_to`, but a proof that
   needs to look at the representation -- a custom allocator, a type pun, two
   views of the same storage -- can always unfold to it.

   This interface is axiomatized: there is no `.fst`. See `palow.md`.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
module SZ = FStar.SizeT

val mem_pts_to ([@@@mkey] a: ptr) (p: perm) (b: bytes) : slprop

val mem_pts_to_timeless (a: ptr) (p: perm) (b: bytes)
  : Lemma (timeless (mem_pts_to a p b))
          [SMTPat (timeless (mem_pts_to a p b))]

(* ---------------------------------------------------------------------------
   Basic facts
   --------------------------------------------------------------------------- *)

(* Owning a non-empty range means the pointer is a real, derived pointer: it is
   not null and it carries the provenance of the allocation it lives in.

   A zero-length range carries no information, which is deliberate: `malloc(0)`
   may return a non-null pointer that cannot be dereferenced, and one-past-the-end
   pointers are legal to form. *)
ghost fn mem_pts_to_not_null (a: ptr) (#p: perm) (#b: bytes)
  preserves mem_pts_to a p b
  requires  pure (len b > 0)
  ensures   pure (not (is_null a) /\ Some? (prov_of a))

(* Addresses of live storage fit in `size_t`, so offset computations inside an
   object never overflow. *)
ghost fn mem_pts_to_fits (a: ptr) (#p: perm) (#b: bytes)
  preserves mem_pts_to a p b
  ensures   pure (SZ.fits (addr_of a + len b))

ghost fn mem_pts_to_perm_bound (a: ptr) (#p: perm) (#b: bytes)
  preserves mem_pts_to a p b
  requires  pure (len b > 0)
  ensures   pure (p <=. 1.0R)

(* Two ranges, at least one of them exclusively owned, cannot overlap. This is
   how Palow recovers non-aliasing: it comes from separation, not from
   provenance, so it holds between two distinct `malloc`s and equally between a
   `malloc`ed block and a local.

   Stated with `p1 == 1.0R` rather than the general `~(p1 +. p2 <=. 1.0R)`
   because writes need full permission anyway, and the restricted form is much
   easier for the prover to apply. *)
[@@allow_ambiguous]
ghost fn mem_pts_to_disjoint (a1 a2: ptr) (#p2: perm) (#b1 #b2: bytes)
  preserves mem_pts_to a1 1.0R b1
  preserves mem_pts_to a2 p2 b2
  requires  pure (len b1 > 0 /\ len b2 > 0)
  ensures   pure (disjoint_ranges a1 (len b1) a2 (len b2))

(* Same base pointer, same bytes: the contents of a range are determined by the
   range. *)
[@@allow_ambiguous]
ghost fn mem_pts_to_injective (a: ptr) (#p1 #p2: perm) (#b1 #b2: bytes)
  preserves mem_pts_to a p1 b1
  preserves mem_pts_to a p2 b2
  requires  pure (len b1 == len b2)
  ensures   pure (b1 == b2)

(* ---------------------------------------------------------------------------
   Fractional permissions

   Permissions are per *range*, not per byte: `mem_pts_to` carries a single `p`
   for the whole of `b`. To give different fractions to different parts of an
   object, split the range with `mem_split` first and then share the pieces.
   --------------------------------------------------------------------------- *)

ghost fn mem_share (a: ptr) (#p: perm) (#b: bytes)
  requires mem_pts_to a p b
  ensures  mem_pts_to a (p /. 2.0R) b ** mem_pts_to a (p /. 2.0R) b

[@@allow_ambiguous]
ghost fn mem_gather (a: ptr) (#p1 #p2: perm) (#b1 #b2: bytes)
  requires mem_pts_to a p1 b1
  requires mem_pts_to a p2 b2
  requires pure (len b1 == len b2)
  ensures  mem_pts_to a (p1 +. p2) b1
  ensures  pure (b1 == b2)

(* ---------------------------------------------------------------------------
   Splitting and joining ranges

   These two are the reason the whole design works: carving a block into
   independently owned pieces is just splitting a byte range, so a pool
   allocator handing out interior pointers of a `malloc`ed block needs no
   special support. They are also what the aggregate field split/join lemmas
   are built from.
   --------------------------------------------------------------------------- *)

ghost fn mem_split (a: ptr) (#p: perm) (#b: bytes) (n: SZ.t { SZ.v n <= len b })
  requires mem_pts_to a p b
  ensures  mem_pts_to a p (slice b 0 (SZ.v n))
  ensures  mem_pts_to (a +! n) p (slice b (SZ.v n) (len b))

ghost fn mem_join (a: ptr) (#p: perm) (#b1 #b2: bytes) (n: SZ.t { SZ.v n == len b1 })
  requires mem_pts_to a p b1
  requires mem_pts_to (a +! n) p b2
  ensures  mem_pts_to a p (append b1 b2)
