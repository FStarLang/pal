module Pulse.Lib.C.Palow.Alloc

(* ---------------------------------------------------------------------------
   Allocated storage.

   The payoff of layer 0: `malloc` is an ordinary function with an ordinary
   specification. It is *not* a special case that has to pattern-match on the
   AST to guess the allocated type, because there is no allocated type -- it
   hands out raw bytes, and the caller claims them at whatever type it likes
   (see `Pulse.Lib.C.Palow.Scalar.uint32_t_claim`).

   Consequently a custom `xmalloc` is specified by writing this same
   postcondition, and needs no support in the translator at all.

   This interface is axiomatized: there is no `.fst`.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Nullable

module SZ = FStar.SizeT

(* The right to return `n` bytes at `a` to the allocator they came from.

   `freeable` deliberately does *not* split: a pool allocator that carves a
   block into chunks publishes its own `pool_freeable` predicate instead, which
   is what stops a caller from passing a `pool_malloc`ed pointer to `free`.
   Keeping the two predicates distinct is the point, not a limitation. *)
val freeable ([@@@mkey] a: ptr) (n: SZ.t) : slprop

val freeable_timeless (a: ptr) (n: SZ.t)
  : Lemma (timeless (freeable a n))
          [SMTPat (timeless (freeable a n))]

(* Allocation may fail, so the postcondition is guarded by nullness. The bytes
   handed back are uninitialized: reading them at any type is blocked, because
   no `*_repr` relates a value to a range containing an uninitialized byte. *)
fn malloc (n: SZ.t)
  returns  a : ptr
  ensures  unless_null a (mem_pts_to a 1.0R (uninit (SZ.v n)) ** freeable a n)

fn calloc (n: SZ.t)
  returns  a : ptr
  ensures  unless_null a (mem_pts_to a 1.0R (zeroed (SZ.v n)) ** freeable a n)

(* `free` needs the whole block back, at full permission, and needs to be told
   nothing about its contents. Requiring `len b == SZ.v n` is what makes
   freeing a strict subrange -- or a pointer into the middle of a block --
   unprovable. *)
fn free (a: ptr) (#n: SZ.t) (#b: bytes { len b == SZ.v n })
  requires freeable a n
  requires mem_pts_to a 1.0R b
