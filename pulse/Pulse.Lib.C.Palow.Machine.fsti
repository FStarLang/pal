module Pulse.Lib.C.Palow.Machine

(* ---------------------------------------------------------------------------
   The machine operations: typed loads, typed stores, and stack allocation.

   These are the genuine primitives of the model -- they correspond to machine
   instructions, so they are axiomatized rather than defined. Everything else
   in Palow is derived. Note that their *specifications* are written entirely in
   terms of the derived layer-1 predicates from
   `Pulse.Lib.C.Palow.Scalar`, which are themselves defined from
   `mem_pts_to`; so the axioms here add operations, not new facts about
   memory.

   PAL will emit one group of these per translated C scalar type.

   This interface is axiomatized: there is no `.fst`.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64

(* ---------------------------------------------------------------------------
   Loads and stores

   The `rewrites_to` in the read postcondition is what makes nested
   dereferences (`**x`) work: the result of the inner read has to be
   definitionally connected to the logical pointee, so that the outer read can
   resolve its own points-to from the context. Returning `pure (y == x)`
   instead would leave the outer `mem_pts_to` unresolvable.
   --------------------------------------------------------------------------- *)

fn uint32_t_read (a: ptr) (#p: perm) (#x: erased U32.t)
  preserves uint32_t_pts_to a p x
  returns  y : U32.t
  ensures  rewrites_to y (reveal x)

fn uint32_t_write (a: ptr) (y: U32.t) (#x: erased U32.t)
  requires uint32_t_pts_to a 1.0R x
  ensures  uint32_t_pts_to a 1.0R y

(* Storing into storage whose previous contents we know nothing about -- the
   first write to a fresh local or to `malloc`ed bytes. A store needs no
   knowledge of what it overwrites, only exclusive ownership of the right
   number of bytes. *)
fn uint32_t_write_uninit (a: ptr) (y: U32.t)
  requires uint32_t_pts_to_uninit a
  ensures  uint32_t_pts_to a 1.0R y

fn uint8_t_read (a: ptr) (#p: perm) (#x: erased U8.t)
  preserves uint8_t_pts_to a p x
  returns  y : U8.t
  ensures  rewrites_to y (reveal x)

fn uint8_t_write (a: ptr) (y: U8.t) (#x: erased U8.t)
  requires uint8_t_pts_to a 1.0R x
  ensures  uint8_t_pts_to a 1.0R y

(* Loading and storing a pointer value. `rewrites_to` matters most here: it is
   what makes `**x` work, since the pointer read out of `x` has to be usable as
   the subject of the next `mem_pts_to` without the caller restating it. *)
fn ptr_read (a: ptr) (#p: perm) (#x: erased ptr)
  preserves ptr_pts_to a p x
  returns  y : ptr
  ensures  rewrites_to y (reveal x)

fn ptr_write (a: ptr) (y: ptr) (#x: erased ptr)
  requires ptr_pts_to a 1.0R x
  ensures  ptr_pts_to a 1.0R y

(* ---------------------------------------------------------------------------
   Byte-wise copying

   `memcpy` is the one place where C is explicit that objects are sequences of
   bytes, and it is the reason layer 0 is stated in terms of bytes at all. The
   spec is as strong as it can be and needs no side conditions about types:
   the destination ends up holding *the same bytes*, which for a stored pointer
   means the same provenance too, so a pointer copied through `memcpy` remains
   dereferenceable. Nothing extra has to be said to get that; see
   `Pulse.Lib.C.Palow.Provenance`.
   --------------------------------------------------------------------------- *)

fn memcpy (dst src: ptr) (n: SZ.t) (#p: perm) (#bs #bd: erased bytes)
  preserves mem_pts_to src p bs
  requires  mem_pts_to dst 1.0R bd
  requires  pure (len bs == SZ.v n /\ len bd == SZ.v n)
  ensures   mem_pts_to dst 1.0R bs

(* ---------------------------------------------------------------------------
   Automatic storage

   Locals get per-type stack allocation and deallocation rather than reusing
   Pulse's own locals: Pulse locals behave differently enough that supporting
   both would be a permanent source of special cases in the translator.

   There is deliberately no token pairing an allocation with its deallocator,
   matching how Pulse's own `let mut` works. Handing a `malloc`ed pointer to
   `uint32_t_stack_free` would indeed be wrong, but PAL controls the
   translation and never emits it, so paying for a token everywhere to rule out
   a program we do not generate is not worth it.
   --------------------------------------------------------------------------- *)

fn uint32_t_stack_alloc ()
  returns  a : ptr
  ensures  uint32_t_pts_to_uninit a

fn uint32_t_stack_free (a: ptr)
  requires uint32_t_pts_to_uninit a

fn ptr_stack_alloc ()
  returns  a : ptr
  ensures  mem_pts_to a 1.0R (uninit (SZ.v ptr_sizeof))

fn ptr_stack_free (a: ptr) (#b: erased bytes)
  requires mem_pts_to a 1.0R b
  requires pure (len b == SZ.v ptr_sizeof)

(* ---------------------------------------------------------------------------
   The remaining C scalar types

   `uint32_t` above is the exemplar; this is the same group for every other
   scalar type, over the layer-1 predicates in `Pulse.Lib.C.Palow.CTypes`.
   `uint8_t`'s read and write are already given above, so it appears here only
   for its uninitialized store and its automatic storage.

   Five operations per type is the whole per-type cost on the machine side: a
   load, two stores (one over a known value, one over storage of unknown
   contents), and an allocate/deallocate pair.
   --------------------------------------------------------------------------- *)

fn bool_t_read (a: ptr) (#p: perm) (#x: erased bool)
  preserves bool_t_pts_to a p x
  returns  y : bool
  ensures  rewrites_to y (reveal x)

fn bool_t_write (a: ptr) (y: bool) (#x: erased bool)
  requires bool_t_pts_to a 1.0R x
  ensures  bool_t_pts_to a 1.0R y

fn bool_t_write_uninit (a: ptr) (y: bool)
  requires bool_t_pts_to_uninit a
  ensures  bool_t_pts_to a 1.0R y

fn bool_t_stack_alloc ()
  returns  a : ptr
  ensures  bool_t_pts_to_uninit a

fn bool_t_stack_free (a: ptr)
  requires bool_t_pts_to_uninit a

fn int8_t_read (a: ptr) (#p: perm) (#x: erased I8.t)
  preserves int8_t_pts_to a p x
  returns  y : I8.t
  ensures  rewrites_to y (reveal x)

fn int8_t_write (a: ptr) (y: I8.t) (#x: erased I8.t)
  requires int8_t_pts_to a 1.0R x
  ensures  int8_t_pts_to a 1.0R y

fn int8_t_write_uninit (a: ptr) (y: I8.t)
  requires int8_t_pts_to_uninit a
  ensures  int8_t_pts_to a 1.0R y

fn int8_t_stack_alloc ()
  returns  a : ptr
  ensures  int8_t_pts_to_uninit a

fn int8_t_stack_free (a: ptr)
  requires int8_t_pts_to_uninit a

fn int16_t_read (a: ptr) (#p: perm) (#x: erased I16.t)
  preserves int16_t_pts_to a p x
  returns  y : I16.t
  ensures  rewrites_to y (reveal x)

fn int16_t_write (a: ptr) (y: I16.t) (#x: erased I16.t)
  requires int16_t_pts_to a 1.0R x
  ensures  int16_t_pts_to a 1.0R y

fn int16_t_write_uninit (a: ptr) (y: I16.t)
  requires int16_t_pts_to_uninit a
  ensures  int16_t_pts_to a 1.0R y

fn int16_t_stack_alloc ()
  returns  a : ptr
  ensures  int16_t_pts_to_uninit a

fn int16_t_stack_free (a: ptr)
  requires int16_t_pts_to_uninit a

fn int32_t_read (a: ptr) (#p: perm) (#x: erased I32.t)
  preserves int32_t_pts_to a p x
  returns  y : I32.t
  ensures  rewrites_to y (reveal x)

fn int32_t_write (a: ptr) (y: I32.t) (#x: erased I32.t)
  requires int32_t_pts_to a 1.0R x
  ensures  int32_t_pts_to a 1.0R y

fn int32_t_write_uninit (a: ptr) (y: I32.t)
  requires int32_t_pts_to_uninit a
  ensures  int32_t_pts_to a 1.0R y

fn int32_t_stack_alloc ()
  returns  a : ptr
  ensures  int32_t_pts_to_uninit a

fn int32_t_stack_free (a: ptr)
  requires int32_t_pts_to_uninit a

fn int64_t_read (a: ptr) (#p: perm) (#x: erased I64.t)
  preserves int64_t_pts_to a p x
  returns  y : I64.t
  ensures  rewrites_to y (reveal x)

fn int64_t_write (a: ptr) (y: I64.t) (#x: erased I64.t)
  requires int64_t_pts_to a 1.0R x
  ensures  int64_t_pts_to a 1.0R y

fn int64_t_write_uninit (a: ptr) (y: I64.t)
  requires int64_t_pts_to_uninit a
  ensures  int64_t_pts_to a 1.0R y

fn int64_t_stack_alloc ()
  returns  a : ptr
  ensures  int64_t_pts_to_uninit a

fn int64_t_stack_free (a: ptr)
  requires int64_t_pts_to_uninit a

fn uint8_t_write_uninit (a: ptr) (y: U8.t)
  requires uint8_t_pts_to_uninit a
  ensures  uint8_t_pts_to a 1.0R y

fn uint8_t_stack_alloc ()
  returns  a : ptr
  ensures  uint8_t_pts_to_uninit a

fn uint8_t_stack_free (a: ptr)
  requires uint8_t_pts_to_uninit a

fn uint16_t_read (a: ptr) (#p: perm) (#x: erased U16.t)
  preserves uint16_t_pts_to a p x
  returns  y : U16.t
  ensures  rewrites_to y (reveal x)

fn uint16_t_write (a: ptr) (y: U16.t) (#x: erased U16.t)
  requires uint16_t_pts_to a 1.0R x
  ensures  uint16_t_pts_to a 1.0R y

fn uint16_t_write_uninit (a: ptr) (y: U16.t)
  requires uint16_t_pts_to_uninit a
  ensures  uint16_t_pts_to a 1.0R y

fn uint16_t_stack_alloc ()
  returns  a : ptr
  ensures  uint16_t_pts_to_uninit a

fn uint16_t_stack_free (a: ptr)
  requires uint16_t_pts_to_uninit a

fn uint64_t_read (a: ptr) (#p: perm) (#x: erased U64.t)
  preserves uint64_t_pts_to a p x
  returns  y : U64.t
  ensures  rewrites_to y (reveal x)

fn uint64_t_write (a: ptr) (y: U64.t) (#x: erased U64.t)
  requires uint64_t_pts_to a 1.0R x
  ensures  uint64_t_pts_to a 1.0R y

fn uint64_t_write_uninit (a: ptr) (y: U64.t)
  requires uint64_t_pts_to_uninit a
  ensures  uint64_t_pts_to a 1.0R y

fn uint64_t_stack_alloc ()
  returns  a : ptr
  ensures  uint64_t_pts_to_uninit a

fn uint64_t_stack_free (a: ptr)
  requires uint64_t_pts_to_uninit a

fn size_t_read (a: ptr) (#p: perm) (#x: erased SZ.t)
  preserves size_t_pts_to a p x
  returns  y : SZ.t
  ensures  rewrites_to y (reveal x)

fn size_t_write (a: ptr) (y: SZ.t) (#x: erased SZ.t)
  requires size_t_pts_to a 1.0R x
  ensures  size_t_pts_to a 1.0R y

fn size_t_write_uninit (a: ptr) (y: SZ.t)
  requires size_t_pts_to_uninit a
  ensures  size_t_pts_to a 1.0R y

fn size_t_stack_alloc ()
  returns  a : ptr
  ensures  size_t_pts_to_uninit a

fn size_t_stack_free (a: ptr)
  requires size_t_pts_to_uninit a
