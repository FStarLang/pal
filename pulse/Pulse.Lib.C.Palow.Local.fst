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
module T = Pulse.Lib.C.Palow.Target
module Seq = FStar.Seq

fn array_stack_alloc (#t: Type0) (t_repr: t -> bytes -> prop) (esize: SZ.t) (ealign: SZ.t { SZ.v ealign > 0 }) (n: SZ.t)
                     (nbytes: SZ.t { SZ.v nbytes == SZ.v esize * SZ.v n })
  requires pure (SZ.v esize % SZ.v ealign == 0 /\ pow2 32 % SZ.v ealign == 0
                 /\ SZ.v esize > 0)
  returns a : ptr
  ensures array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) (SZ.v ealign) a 1.0R
                       (Seq.create (SZ.v n) (None #t))
  ensures pure (addr_of a + SZ.v nbytes < T.addr_limit /\ not (is_null a))
{
  let a = mem_stack_alloc nbytes ealign;
  mem_pts_to_fits a;
  array_claim_uninit t_repr a esize ealign n;
  a
}

fn array_stack_free (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                    (#xs: erased (Seq.seq (option t)))
  requires array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) (SZ.v ealign) a 1.0R xs
{
  array_forget t_repr a esize ealign;
  mem_stack_free a;
}


(* ---------------------------------------------------------------------------
   Zeroing an array

   `memset(a, 0, n * sizeof(t))` is the same join: the machine layer knows how
   to make a byte range all-zero, and the array layer knows what an all-zero
   byte range means element by element. Neither half is new -- `elem_bytes_zeroed`
   is the lemma `calloc` already needed -- so this is a wrapper rather than an
   axiom, and it reads through `array_claim_zeroed`'s obligation: which value
   the elements end up holding is whatever the element type's representation
   makes of an all-zero range, which the caller names with `encode_zero`.

   Only the fill value 0 is covered, which is the fill C code reliably means:
   `memset` with anything else is well defined only for byte-sized types. *)
fn array_memset_zero (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr)
                     (esize: SZ.t) (ealign: SZ.t) (n: SZ.t) (nbytes: SZ.t)
                     (z: t)
                     (* `xs` is `erased` because this is not a ghost function:
                        an implicit Pulse cannot erase has to be instantiated
                        at every call, and failing to gives a misleading
                        "cannot have a ghost effect". *)
                     (#xs: erased (Seq.seq t))
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a 1.0R xs
  requires pure (Seq.length xs == SZ.v n /\ SZ.v nbytes == SZ.v esize * SZ.v n)
  requires pure (t_repr z (zeroed (SZ.v esize)))
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a 1.0R (Seq.create (SZ.v n) z)
{
  unfold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a 1.0R xs;
  memset_zero a nbytes;
  Classical.forall_intro (Classical.move_requires (elem_bytes_zeroed (SZ.v esize) (SZ.v n)));
  fold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a 1.0R (Seq.create (SZ.v n) z);
}

(* A value under a fresh name, related to the original by an ordinary equality
   rather than by substitution. A call whose postcondition `rewrites_to` its
   result as a term over the callee's post-state witnesses hands the caller a
   value that *is* that term. Stored in a local inside one arm of an `if`, it
   ties the local's points-to to those witnesses, and Pulse's join then
   abstracts the witnesses apart from the ownership they also index. PAL stores
   the copy instead. *)
inline_for_extraction
fn value_copy (#t: Type0) (x: t)
  returns y : t
  ensures pure (y == x)
{
  x
}

(* ---------------------------------------------------------------------------
   A fact carried across the join of an `if`

   Pulse joins an `if` by itself, keeping what the arms own but not what they
   proved about it: a value each arm stored with a known bound is a fresh
   value after the join, about which nothing is known. Held as a resource the
   fact is part of what the arms own, so the join keeps it -- stated at the
   same existential as the points-to it is about -- and it is put back into
   the context right after.
   --------------------------------------------------------------------------- *)
let if_fact (p: prop) : slprop = pure p

ghost fn intro_if_fact (p: prop)
  requires pure p
  ensures if_fact p
{
  fold (if_fact p);
}

ghost fn elim_if_fact (p: prop)
  requires if_fact p
  ensures pure p
{
  unfold (if_fact p);
}
