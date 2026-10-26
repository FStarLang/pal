module Pulse.Lib.C.Palow.Provenance

(* ---------------------------------------------------------------------------
   Worked examples for provenance.

   Two things are demonstrated here, both of which are *theorems* about the
   model rather than axioms:

   1. `round_trip` -- a pointer cast to `uintptr_t` and back is the pointer we
      started with, provided the allocation was exposed first. This is the
      whole point of the exposure discipline: exposure is not a fiction we
      carry around, it actually buys the round trip.

   2. `transport` -- acceptance test 5 from `palow.md`. A stored pointer copied
      byte-wise with `memcpy` into fresh untyped allocated storage is still
      dereferenceable at the destination. Nothing in `memcpy`'s spec mentions
      provenance; it falls out of the destination holding the same bytes.
      Its effective-type rule additionally needs an established source.

   The second is worth dwelling on. Under a model where the object
   representation is a sequence of plain `uint8_t`s, this program is not
   provable: the bytes at the destination determine the address but not which
   allocation it belongs to, so the recovered pointer has nothing to license a
   dereference. Adding provenance to `byte` is exactly what closes that gap,
   and it costs `memcpy` nothing -- its spec is the one you would have written
   anyway.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Encoding
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.Machine
open Pulse.Lib.C.Palow.Expose

module U32 = FStar.UInt32
module SZ = FStar.SizeT
module ET = Pulse.Lib.C.Palow.Etype
module V = Pulse.Lib.C.Palow.Effective.Value
module Seq = FStar.Seq

(* `(uintptr_t) a` followed by a cast back yields `a` itself. Note where the
   ownership is used: `expose` and `mem_pts_to_footprint` both need it, but
   `ptr_to_uintptr` does not -- taking an address is harmless, using the result
   is not. *)
fn round_trip (a: ptr) (#p: perm) (#x: erased U32.t)
  preserves uint32_t_pts_to a p x
  returns   b : ptr
  ensures   pure (b == a)
{
  uint32_t_reveal a;
  expose a;
  mem_pts_to_footprint a;
  let n = ptr_to_uintptr a;
  let b = uintptr_to_ptr n (hide (prov_of a));
  ptr_ext a b;
  uint32_t_conceal a #p #_ #(reveal x);
  drop_ (exposed (prov_of a));
  b
}

(* The source has an established pointer type; mere fallback readability is
   not sufficient to establish the destination's type through copying. *)
fn transport (src dst: ptr) (#target: ptr) (#bd: bytes) (#x: erased U32.t)
  requires V.value ptr_ctype ptr_repr ptr_alignof src 1.0R target
    (ET.etypes_of ptr_ctype true)
  requires mem_pts_to_at dst 1.0R bd (Seq.create 8 None)
  requires pure (len bd == SZ.v ptr_sizeof /\ aligned dst ptr_alignof)
  preserves uint32_t_pts_to target 1.0R x
  returns   y : U32.t
  ensures V.value ptr_ctype ptr_repr ptr_alignof src 1.0R target
    (ET.etypes_of ptr_ctype true) ** ptr_pts_to dst 1.0R target
  ensures   pure (y == reveal x)
{
  V.reveal_value ptr_ctype ptr_repr ptr_alignof src;
  with bs. assert (mem_pts_to_at src 1.0R bs (ET.etypes_of ptr_ctype true));
  memcpy dst src ptr_sizeof;
  V.claim ptr_ctype ptr_repr ptr_alignof src #1.0R #target #bs
    #(ET.etypes_of ptr_ctype true);
  ptr_conceal dst #1.0R #_ #target;
  let p = ptr_read dst;
  uint32_t_read p;
}
