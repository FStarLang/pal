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

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32

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

(* ---------------------------------------------------------------------------
   Automatic storage

   Locals get per-type stack allocation and deallocation rather than reusing
   Pulse's own locals: Pulse locals behave differently enough that supporting
   both would be a permanent source of special cases in the translator. The
   `stack_freeable` token is what prevents a heap pointer from being returned
   to the stack allocator, and vice versa.
   --------------------------------------------------------------------------- *)

val stack_freeable ([@@@mkey] a: ptr) (n: SZ.t) : slprop

val stack_freeable_timeless (a: ptr) (n: SZ.t)
  : Lemma (timeless (stack_freeable a n))
          [SMTPat (timeless (stack_freeable a n))]

fn uint32_t_stack_alloc ()
  returns  a : ptr
  ensures  uint32_t_pts_to_uninit a
  ensures  stack_freeable a uint32_t_sizeof

fn uint32_t_stack_free (a: ptr)
  requires uint32_t_pts_to_uninit a
  requires stack_freeable a uint32_t_sizeof
