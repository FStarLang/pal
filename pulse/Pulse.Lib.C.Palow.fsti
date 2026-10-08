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
module Seq = FStar.Seq
module Etype = Pulse.Lib.C.Palow.Etype

(* Ownership of a range of bytes, together with the per-byte effective-type
   index those bytes carry (see `Pulse.Lib.C.Palow.Etype`). The index is part
   of the *primitive* notion rather than something layered on afterwards, for
   a reason worth spelling out: if there were an index-free `mem_pts_to` with
   an axiom recovering an index from it, then forgetting an index and
   recalling a fresh one would launder the whole thing -- in particular a
   declared object's `fixed` flag could be dropped, and the object retyped.
   There is no such axiom because there is no such predicate: `mem_pts_to` is
   a *definition*, so an index can be hidden but never conjured. *)
val mem_pts_to_at ([@@@mkey] a: ptr) (p: perm) (b: bytes) (e: Etype.etypes) : slprop

val mem_pts_to_at_timeless (a: ptr) (p: perm) (b: bytes) (e: Etype.etypes)
  : Lemma (timeless (mem_pts_to_at a p b e))
          [SMTPat (timeless (mem_pts_to_at a p b e))]

(* Ownership of the bytes, not caring what the index is. Everything that only
   transports bytes -- padding, `memcpy`, allocation, the aggregate and array
   split/join machinery -- is stated in terms of this and never mentions an
   index. *)
val mem_pts_to ([@@@mkey] a: ptr) (p: perm) (b: bytes) : slprop

(* ...and it is exactly the indexed one with the index hidden. Stated as an
   slprop *equality* rather than as a pair of ghost steps: an equality cannot
   be used to launder an index, because it does not let the two sides drift
   apart, whereas a `forget`/`recall` pair between two independent predicates
   would let an index be discarded and a fresh unconstrained one conjured --
   `fixed` and all. It is an equality rather than a definition only because
   Pulse's frame matcher keys on the head symbol of a `val`, and making this
   one a `let` costs more in matching than the index is worth.

   The index is also required to be `allocated` -- no byte of it is at a
   declared type. That is what makes the unindexed view the view of *storage*:
   allocated storage is the only thing whose index may be forgotten and later
   recovered without losing information a later store would need, since a
   `fixed` entry constrains every future store and an existential over indices
   cannot preserve it. The consequence is that an object with a declared type
   does not pass through this view at all; it needs an indexed path of its
   own. *)
val mem_pts_to_at_eq (a: ptr) (p: perm) (b: bytes)
  : Lemma (mem_pts_to a p b ==
           (exists* e. mem_pts_to_at a p b e
                    ** pure (Etype.elen e == len b /\ Etype.allocated e)))

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
(* ... and, as the flip side of that, a zero-length range *is* `emp`. Every
   axiom in this file that says something about an address is guarded by
   `len b > 0` for exactly this reason, and `mem_pts_to_fits` -- which is not --
   says nothing new at length zero, because `addr_of_bound` already puts every
   address below `pow2 64`.

   This matters because C has objects of size zero: GCC and Clang both accept
   a struct with no members, and real code uses them. Without this equation the
   points-to of such an object would be underivable -- there would be no way to
   obtain the zero-length range it is made of -- and PAL would have to special-
   case empty structs all the way down instead of generating them like any
   other aggregate. *)
val mem_pts_to_empty (a: ptr) (p: perm) (b: bytes)
  : Lemma (requires len b == 0)
          (ensures  mem_pts_to a p b == emp)

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

(* The same fact over the indexed view. It is stated here rather than derived
   in `Pulse.Lib.C.Palow.Index` because the derivation there would have to
   spend the resource that knows the index -- observing through half of a
   share shows only `p /. 2.0R <=. 1.0R`, and hiding the index to use the
   layer-0 fact cannot get it back. *)
ghost fn mem_pts_to_at_perm_bound (a: ptr) (#p: perm) (#b: bytes) (#e: Etype.etypes)
  preserves mem_pts_to_at a p b e
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

(* ---------------------------------------------------------------------------
   Effective types

   `mem_pts_to_at` is `mem_pts_to` refined with a per-byte effective-type index
   (see `Pulse.Lib.C.Palow.Etype` for the index itself and for the access
   rules). It is here now, rather than later, because it is the one change to
   layer 0 that cannot be made cheaply after the fact: adding an index to
   `mem_pts_to` touches every module in the stack.

   In this first cut the index is present but not *enforced*: no layer-1
   predicate constrains it, so `mem_pts_to` -- which hides it -- is all anyone
   uses, and every existing proof goes through unchanged. Turning enforcement
   on means making the typed loads and stores in `Pulse.Lib.C.Palow.Machine`
   demand `Etype.read_ok` and produce `Etype.store_etypes`, and making each
   typed points-to carry `read_ok e t_ctype` for the index it holds. The
   aggregate, array and union lemmas do not mention the index at all, since
   splitting and joining bytes splits and joins the index alongside them.
   --------------------------------------------------------------------------- *)

(* Splitting a range splits its index at the same point. This is the reason the
   aggregate and array lemmas survive the addition of effective types untouched:
   they are stated over `mem_pts_to`, and the index follows the bytes.

   `mem_split` and `mem_join` above are consequences of these two rather than
   independent assumptions -- unfold, split the index with the bytes, fold --
   and are stated separately only because this module has no implementation to
   derive them in. *)
ghost fn mem_split_at (a: ptr) (#p: perm) (#b: bytes)
                      (#e: Etype.etypes { Etype.elen e == len b })
                      (n: SZ.t { SZ.v n <= len b })
  requires mem_pts_to_at a p b e
  ensures  mem_pts_to_at a p (slice b 0 (SZ.v n)) (Seq.slice e 0 (SZ.v n))
  ensures  mem_pts_to_at (a +! n) p (slice b (SZ.v n) (len b))
                         (Seq.slice e (SZ.v n) (Etype.elen e))

(* The bytes at an address determine their index, just as they determine each
   other (`mem_pts_to_injective`). This is what makes the equality above safe
   to use in both directions: eliminating the existential gives you *the*
   index, not merely *an* index.

   It concludes the byte half as well, under the same length hypothesis
   `mem_pts_to_injective` uses. That is not a second axiom so much as the
   indexed reading of the first: a caller holding two indexed views cannot
   reach the unindexed fact without spending one of them on a rewrite, and
   then has no way to recover the index it gave up. *)
[@@allow_ambiguous]
ghost fn mem_pts_to_at_injective (a: ptr) (#p1 #p2: perm) (#b1 #b2: bytes)
                                 (#e1 #e2: Etype.etypes)
  preserves mem_pts_to_at a p1 b1 e1
  preserves mem_pts_to_at a p2 b2 e2
  ensures   pure (e1 == e2 /\ (len b1 == len b2 ==> b1 == b2))

ghost fn mem_join_at (a: ptr) (#p: perm) (#b1 #b2: bytes)
                     (#e1: Etype.etypes { Etype.elen e1 == len b1 })
                     (#e2: Etype.etypes { Etype.elen e2 == len b2 })
                     (n: SZ.t { SZ.v n == len b1 })
  requires mem_pts_to_at a p b1 e1 ** mem_pts_to_at (a +! n) p b2 e2
  ensures  mem_pts_to_at a p (append b1 b2) (Seq.append e1 e2)

(* Sharing and gathering carry the index along unchanged. These two cannot be
   derived from `mem_pts_to_at_eq` the way the splitting lemmas can, and the
   reason is worth recording, because it is the same reason the equality is
   safe in the first place.

   Going `mem_pts_to_at a p b e` -> `mem_pts_to a p b` -> share -> and back
   produces two halves whose indices are existentially quantified. They can be
   shown equal to each other, by `mem_pts_to_at_injective`, but not to `e`:
   the resource that knew about `e` was spent by the rewrite, and an
   existential cannot be forced to a particular witness after the fact. That
   inability is precisely what stops `hide` followed by `show` from being a
   laundering step -- so it is not a defect to be worked around here, and the
   honest response is to state the indexed forms as primitive.

   Everything else that merely *observes* a range -- nullness, bounds,
   disjointness, injectivity -- is derived from these in
   `Pulse.Lib.C.Palow.Index`, by sharing, observing through one half, and
   gathering back. *)
ghost fn mem_share_at (a: ptr) (#p: perm) (#b: bytes) (#e: Etype.etypes)
  requires mem_pts_to_at a p b e
  ensures  mem_pts_to_at a (p /. 2.0R) b e ** mem_pts_to_at a (p /. 2.0R) b e

[@@allow_ambiguous]
ghost fn mem_gather_at (a: ptr) (#p1 #p2: perm) (#b1 #b2: bytes)
                       (#e1 #e2: Etype.etypes)
  requires mem_pts_to_at a p1 b1 e1
  requires mem_pts_to_at a p2 b2 e2
  requires pure (len b1 == len b2)
  ensures  mem_pts_to_at a (p1 +. p2) b1 e1
  ensures  pure (b1 == b2 /\ e1 == e2)

(* A store at type `u` relabels allocated storage and leaves declared objects
   alone; a read at `u` requires the covered entries to be compatible with it.
   These are the two hooks the typed operations in `Pulse.Lib.C.Palow.Machine`
   will take once enforcement is switched on. *)
ghost fn mem_store_etypes (a: ptr) (#b: bytes) (#e: Etype.etypes)
                          (u: Etype.ctype { Etype.elen e == Etype.csize u })
  requires mem_pts_to_at a 1.0R b e
  ensures  mem_pts_to_at a 1.0R b (Etype.store_etypes e u)
