module Pulse.Lib.C.Palow.Expose

(* ---------------------------------------------------------------------------
   The "ae" of PNVI-ae-udi: address exposure.

   Casting a pointer to `uintptr_t` and back is legal C, and real code does it
   (tagged pointers, alignment by masking, hash tables keyed on addresses).
   Under a provenance model it cannot be free, because the integer has no
   provenance to give back: if any integer could be turned into a usable
   pointer, provenance would carry no information at all.

   PNVI-ae resolves this by *exposing* an allocation when a pointer into it is
   cast to an integer. Only exposed allocations can be reconstructed from an
   integer. Here that is a duplicable, monotonic slprop, which is precisely how
   a "once true, always true" fact is modelled in Pulse.

   The "udi" (user disambiguation) part -- the nondeterministic choice among
   several exposed allocations whose footprints contain the same address,
   resolved by how the resulting pointer is subsequently used -- collapses in a
   verification setting: the caller passes the intended allocation as a ghost
   argument, and that choice *is* the disambiguation, made statically instead
   of by the semantics.

   This interface is axiomatized: there is no `.fst`. Exposure is a property of
   the machine and its allocator, not of any program.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow

module SZ = FStar.SizeT

(* `q` has had one of its addresses observed as an integer. Duplicable and
   never revoked: an allocation that has been exposed stays exposed for as long
   as it lives, so this may be freely shared and never has to be given back.

   This is indexed by a `prov`, not an `alloc_id`, purely so that every
   signature below can be written in terms of `prov_of a` without a `Some?`
   refinement on the binder. `exposed None` is harmless: it is `in_footprint`
   that decides whether an integer can become a *usable* pointer, and
   `in_footprint None x` is never provable, since the only way to establish
   `in_footprint` is `mem_pts_to_footprint`, which needs ownership and hence a
   real allocation. *)
val exposed (q: prov) : slprop

val exposed_timeless (q: prov)
  : Lemma (timeless (exposed q))
          [SMTPat (timeless (exposed q))]

ghost fn exposed_dup (q: prov)
  requires exposed q
  ensures  exposed q ** exposed q

(* `x` is an address belonging to allocation `q` (including one past its end,
   which C allows to be formed but not dereferenced). *)
val in_footprint (q: prov) (x: nat) : prop

(* Owning a non-empty range means its base address is inside the allocation the
   pointer came from -- so a pointer recovered from that address via
   `uintptr_to_ptr` is the pointer we started with. Without this the round trip
   would type-check but be useless, since nothing would connect the integer
   back to a footprint. *)
ghost fn mem_pts_to_footprint (a: ptr) (#p: perm) (#b: bytes)
  preserves mem_pts_to a p b
  requires  pure (len b > 0)
  ensures   pure (in_footprint (prov_of a) (addr_of a))

(* ---------------------------------------------------------------------------
   The round trip
   --------------------------------------------------------------------------- *)

(* Exposure is a ghost step: it records that the allocation's address may
   escape, but compiles to nothing. It needs ownership of some of the
   allocation, which is how we know the allocation is live and which one it is. *)
ghost fn expose (a: ptr) (#p: perm) (#b: bytes)
  preserves mem_pts_to a p b
  requires  pure (len b > 0)
  ensures   exposed (prov_of a)

(* `(uintptr_t) a`. Yields the address and, as a side effect, exposes the
   allocation. Note that it needs no ownership: taking the address of a dangling
   pointer is not itself undefined, only using the result is. But it does need
   the allocation to have been exposed already, which in practice comes from
   `expose` on the same pointer. *)
fn ptr_to_uintptr (a: ptr)
  preserves exposed (prov_of a)
  returns   n : SZ.t
  ensures   pure (SZ.v n == addr_of a)

(* Casting an integer back to a pointer type. The ghost `q` says which exposed
   allocation the integer is meant to denote; `in_footprint` says the address
   really is one of that allocation's. Together they reconstruct the pointer,
   provenance and all.

   Passing `q` is what stands in for PNVI-ae-udi's "user disambiguation": where
   the semantics nondeterministically picks among the exposed allocations whose
   footprint contains the address and lets subsequent use decide, we make the
   choice statically at the cast. *)
fn uintptr_to_ptr (n: SZ.t) (q: erased prov)
  preserves exposed q
  requires  pure (in_footprint q (SZ.v n))
  returns   a : ptr
  ensures   pure (addr_of a == SZ.v n /\ prov_of a == reveal q)
