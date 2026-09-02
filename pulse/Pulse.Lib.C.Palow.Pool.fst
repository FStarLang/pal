module Pulse.Lib.C.Palow.Pool

(* ---------------------------------------------------------------------------
   Acceptance test: a custom allocator.

   A bump allocator that takes a block of bytes and hands out `uint32_t`
   objects from it. This is the test `palow.md` names as the main motivation
   for the whole design, and it is written here with *no* support from the
   translator and no new axioms: `pool_alloc_uint32` is an ordinary Pulse
   function, and its correctness comes entirely from `mem_split` plus the
   layer-1 claim operation.

   Under the current model this program cannot even be stated, because a
   pointer's type is baked into its ownership predicate and there is no way to
   turn one allocation of N bytes into several independently owned typed
   objects.

   Note also what the specification does *not* say: nothing here entitles a
   client to pass a pool-allocated pointer to `free`. The pool hands out bare
   `uint32_t_pts_to_uninit`, never `Alloc.freeable`, so `free` on a chunk is
   simply unprovable -- which is the reason `freeable` does not split.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.Nullable

module SZ = FStar.SizeT
module U32 = FStar.UInt32
module R = Pulse.Lib.Reference

(* The pool's state: the next address to hand out, and how many bytes are left
   there. The resource invariant ties the two together with ownership of
   exactly that many bytes. *)
let pool_inv (rp: R.ref ptr) (rn: R.ref SZ.t) : slprop =
  exists* (a: ptr) (n: SZ.t) (b: bytes).
    R.pts_to rp a ** R.pts_to rn n ** mem_pts_to a 1.0R b **
    pure (len b == SZ.v n)

ghost fn pool_intro (rp: R.ref ptr) (rn: R.ref SZ.t) (#a: ptr) (#n: SZ.t) (#b: bytes)
  requires R.pts_to rp a ** R.pts_to rn n ** mem_pts_to a 1.0R b
  requires pure (len b == SZ.v n)
  ensures  pool_inv rp rn
{
  fold pool_inv rp rn;
}

(* Hand out one `uint32_t`-sized chunk, or null if the pool is exhausted.

   The whole proof is: split the remaining range at 4 bytes, keep the tail in
   the invariant, and claim the head as uninitialized `uint32_t` storage. *)
#push-options "--z3rlimit 40"
fn pool_alloc_uint32 (rp: R.ref ptr) (rn: R.ref SZ.t)
  requires pool_inv rp rn
  returns  res : ptr
  ensures  pool_inv rp rn
  ensures  unless_null res (uint32_t_pts_to_uninit res)
{
  unfold pool_inv rp rn;
  with a n b. assert (R.pts_to rp a ** R.pts_to rn n ** mem_pts_to a 1.0R b);
  let cur = !rp;
  let rem = !rn;
  if (SZ.gte rem uint32_t_sizeof) {
    mem_pts_to_not_null cur;
    assert (pure (not (is_null cur)));
    mem_split cur uint32_t_sizeof;
    rp := cur +! uint32_t_sizeof;
    rn := SZ.sub rem uint32_t_sizeof;
    fold pool_inv rp rn;
    uint32_t_claim_uninit cur;
    intro_unless_null cur (uint32_t_pts_to_uninit cur);
    cur
  } else {
    fold pool_inv rp rn;
    intro_unless_null_null null (uint32_t_pts_to_uninit null);
    null
  }
}
#pop-options

(* A custom allocator can be handed to code that only knows the `malloc`-shaped
   specification: `pool_alloc_uint32` produces exactly the resource a first
   store into a fresh local or heap cell consumes. *)
fn pool_alloc_and_store (rp: R.ref ptr) (rn: R.ref SZ.t) (v: U32.t)
  requires pool_inv rp rn
  returns  res : ptr
  ensures  pool_inv rp rn
  ensures  unless_null res (uint32_t_pts_to res 1.0R v)
{
  let a = pool_alloc_uint32 rp rn;
  if (is_null a) {
    elim_unless_null_null a (uint32_t_pts_to_uninit a);
    intro_unless_null_null a (uint32_t_pts_to a 1.0R v);
    a
  } else {
    elim_unless_null a (uint32_t_pts_to_uninit a);
    Pulse.Lib.C.Palow.Machine.uint32_t_write_uninit a v;
    intro_unless_null a (uint32_t_pts_to a 1.0R v);
    a
  }
}
