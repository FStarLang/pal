module Pulse.Lib.C.Palow.Local
(* ---------------------------------------------------------------------------
   Automatic storage for an array

   `Pulse.Lib.C.Palow.Array` says what a partially initialised array *is*, but
   it cannot say where the storage comes from: the machine layer depends on the
   scalar layer, which depends on the array layer, so the allocation primitives
   are downstream of everything here. These two wrappers are the join point,
   and they are the whole of it -- there is no new axiom for an array local,
   only `mem_stack_alloc` plus the fold in `array_claim_uninit`.

   The byte count is passed in rather than computed, for the same reason
   `array_split` takes its offset: PAL always knows it statically, and the
   multiplication's overflow proof belongs where the number is known.
   --------------------------------------------------------------------------- *)
#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Array
open Pulse.Lib.C.Palow.Machine

module SZ = FStar.SizeT
module Seq = FStar.Seq

fn array_stack_alloc (#t: Type0) (t_repr: t -> bytes -> prop) (esize: SZ.t) (n: SZ.t)
                     (nbytes: SZ.t { SZ.v nbytes == SZ.v esize * SZ.v n })
  returns a : ptr
  ensures array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) a 1.0R
                       (Seq.create (SZ.v n) (None #t))
{
  let a = mem_stack_alloc nbytes;
  array_claim_uninit t_repr a esize n;
  a
}

fn array_stack_free (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t)
                    (#xs: Seq.seq (option t))
  requires array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) a 1.0R xs
{
  array_forget t_repr a esize;
  mem_stack_free a;
}

