module Pulse.Lib.C.Palow.Overread
(* ---------------------------------------------------------------------------
   TRUSTED: reading an aligned word that may extend past the end of an array

   The fast `strlen` reads the string a word at a time from an aligned
   address and stops at the word that holds the terminator. That word may
   reach past the end of the object: ISO C says the behaviour is undefined,
   and the memory model agrees -- there is no `mem_pts_to` for the bytes
   beyond the array, so `Pulse.Lib.C.Palow.Word` cannot prove such a read.
   On real hardware it is harmless, because memory protection works in whole
   pages, a page is a multiple of the word size, and an aligned word therefore
   never straddles a page boundary: if its first byte is readable, so is the
   rest.

   That last argument is about hardware, not about C, so it cannot be proved
   here. This interface ASSUMES it, and has no `.fst`. PAL emits a call to it
   only in a function marked `_pal_overread`, which is where the user accepts
   the assumption; everywhere else a word read must lie inside the array.

   What the axiom gives is deliberately weak:
   - the word's address is aligned for the word, and its first byte is an
     element of the array (`pos < length`);
   - the result agrees with the array on the bytes that are inside it
     (`word_bytes_upto`), and nothing is said about the others;
   - the read takes and returns the array's ownership unchanged.
   It is consistent: for any array there is such a value, the one whose
   in-bounds bytes are the elements and whose other bytes are zero.
   --------------------------------------------------------------------------- *)
#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes
open Pulse.Lib.C.Palow.Array
open Pulse.Lib.C.Palow.Word

module SZ = FStar.SizeT
module Seq = FStar.Seq
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

fn array_overread_uint16_t (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                     (bl: squash (bytelike t_repr ev ef))
                     (a: ptr) (esize ealign: SZ.t) (q: ptr) (#p: perm) (#xs: erased (Seq.seq t))
                     (w: SZ.t { SZ.v w == 2 /\ SZ.v esize == 1 /\ walk_ok 1 a q /\
                                walk_idx 1 a q < Seq.length xs })
  preserves array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  requires pure (addr_of q % SZ.v uint16_t_alignof == 0)
  returns  x : U16.t
  ensures  pure (word_bytes_upto ev xs (walk_idx 1 a q) (SZ.v w) (U16.v x))

fn array_overread_uint32_t (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                     (bl: squash (bytelike t_repr ev ef))
                     (a: ptr) (esize ealign: SZ.t) (q: ptr) (#p: perm) (#xs: erased (Seq.seq t))
                     (w: SZ.t { SZ.v w == 4 /\ SZ.v esize == 1 /\ walk_ok 1 a q /\
                                walk_idx 1 a q < Seq.length xs })
  preserves array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  requires pure (addr_of q % SZ.v uint32_t_alignof == 0)
  returns  x : U32.t
  ensures  pure (word_bytes_upto ev xs (walk_idx 1 a q) (SZ.v w) (U32.v x))

fn array_overread_uint64_t (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                     (bl: squash (bytelike t_repr ev ef))
                     (a: ptr) (esize ealign: SZ.t) (q: ptr) (#p: perm) (#xs: erased (Seq.seq t))
                     (w: SZ.t { SZ.v w == 8 /\ SZ.v esize == 1 /\ walk_ok 1 a q /\
                                walk_idx 1 a q < Seq.length xs })
  preserves array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  requires pure (addr_of q % SZ.v uint64_t_alignof == 0)
  returns  x : U64.t
  ensures  pure (word_bytes_upto ev xs (walk_idx 1 a q) (SZ.v w) (U64.v x))

fn array_overread_size_t (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                     (bl: squash (bytelike t_repr ev ef))
                     (a: ptr) (esize ealign: SZ.t) (q: ptr) (#p: perm) (#xs: erased (Seq.seq t))
                     (w: SZ.t { SZ.v w == (SZ.v size_t_sizeof) /\ SZ.v esize == 1 /\ walk_ok 1 a q /\
                                walk_idx 1 a q < Seq.length xs })
  preserves array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  requires pure (addr_of q % SZ.v size_t_alignof == 0)
  returns  x : SZ.t
  ensures  pure (word_bytes_upto ev xs (walk_idx 1 a q) (SZ.v w) (SZ.v x))
