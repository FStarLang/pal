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
      byte-wise with `memcpy` into an object of an unrelated type is still
      dereferenceable at the destination. Nothing in `memcpy`'s spec mentions
      pointers or provenance; it falls out of the destination holding the same
      *bytes*, and bytes carrying provenance.

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

(* Acceptance test 5. `src` holds a pointer to a `uint32_t`; `dst` is eight
   bytes of storage of no particular type. After copying the bytes across, the
   pointer read back out of `dst` can be dereferenced -- and `rewrites_to` on
   `ptr_read` means we never have to say that it equals `target`, it just is. *)
fn transport (src dst: ptr) (#target: ptr) (#bd: bytes) (#x: erased U32.t)
  requires ptr_pts_to src 1.0R target
  requires mem_pts_to dst 1.0R bd ** pure (len bd == SZ.v ptr_sizeof)
  preserves uint32_t_pts_to target 1.0R x
  returns   y : U32.t
  ensures   ptr_pts_to src 1.0R target ** ptr_pts_to dst 1.0R target
  ensures   pure (y == reveal x)
{
  unfold ptr_pts_to src 1.0R target;
  memcpy dst src ptr_sizeof;
  fold ptr_pts_to src 1.0R target;
  fold ptr_pts_to dst 1.0R target;
  let p = ptr_read dst;
  uint32_t_read p;
}
