module Pulse.Lib.C.Palow.Array

(* ---------------------------------------------------------------------------
   Palow layer 1: arrays.

   Unlike scalars and structs, arrays need *no* per-type definitions. An array
   of `n` elements of type `t` is the same combinator applied to `t`'s own
   representation relation and element size, so PAL emits nothing at all for an
   array type -- it just instantiates `array_repr` with the element's `t_repr`.

   That is a real simplification over the current model, where `T[N]` has its
   own F* type (`full_array_lspec T N`), its own size axiom, and a pointer-kind
   distinction (`_array` vs `_arrayptr`) that exists precisely because the F*
   type of a variable changes depending on how it is used.

   Splitting an array at an index is just `mem_split` at the corresponding byte
   offset, so subarrays, `a + i` pointer arithmetic and per-element ownership
   all come from layer 0 rather than from array-specific axioms.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow

module SZ = FStar.SizeT
module Seq = FStar.Seq
module M = FStar.Math.Lemmas

(* ---------------------------------------------------------------------------
   The representation relation
   --------------------------------------------------------------------------- *)

(* The byte range occupied by element `i` of an array with `esize`-byte
   elements. Total, returning the empty range when `i` is out of bounds: no
   `*_repr` relation accepts an empty range for a non-empty type, so
   `array_repr` below still says what it should, and making this total avoids
   dragging a bounds proof through every use site. *)
let elem_bytes (esize: nat) (b: bytes) (i: nat) : bytes =
  let lo = esize * i in
  let hi = lo + esize in
  if hi <= len b then slice b lo hi else Seq.empty

let array_repr (#t: Type) (t_repr: t -> bytes -> prop) (esize: nat)
               (xs: Seq.seq t) (b: bytes) : prop =
  len b == esize * Seq.length xs /\
  (forall (i: nat). i < Seq.length xs ==> t_repr (Seq.index xs i) (elem_bytes esize b i))

let array_pts_to (#t: Type) (t_repr: t -> bytes -> prop) (esize: nat)
                 ([@@@mkey] a: ptr) (p: perm) (xs: Seq.seq t) : slprop =
  exists* b. mem_pts_to a p b ** pure (array_repr t_repr esize xs b)

(* ---------------------------------------------------------------------------
   Arithmetic helpers

   These three are the entire nonlinear content of the module: `esize * (i+1)`
   is monotone in `i`, so element `i` of an `n`-element array lies within the
   first `esize * n` bytes.
   --------------------------------------------------------------------------- *)

let elem_fits (esize: nat) (n: nat) (i: nat)
  : Lemma (requires i < n)
          (ensures  esize * i + esize <= esize * n)
  = M.distributivity_add_right esize i 1;
    M.lemma_mult_le_right esize (i + 1) n

let elem_bytes_prefix (esize: nat) (b: bytes) (n: nat) (i: nat)
  : Lemma (requires esize * n <= len b /\ i < n)
          (ensures  elem_bytes esize (slice b 0 (esize * n)) i == elem_bytes esize b i)
  = elem_fits esize n i;
    Seq.slice_slice b 0 (esize * n) (esize * i) (esize * i + esize)

let elem_bytes_suffix (esize: nat) (b: bytes) (n: nat) (i: nat)
  : Lemma (requires esize * n <= len b /\ esize * (n + i) + esize <= len b)
          (ensures  elem_bytes esize (slice b (esize * n) (len b)) i
                    == elem_bytes esize b (n + i))
  = M.distributivity_add_right esize n i;
    Seq.slice_slice b (esize * n) (len b) (esize * i) (esize * i + esize)

(* ---------------------------------------------------------------------------
   Splitting and joining the representation
   --------------------------------------------------------------------------- *)

#push-options "--z3rlimit 40"
let array_repr_split (#t: Type) (t_repr: t -> bytes -> prop) (esize: nat)
                     (xs: Seq.seq t) (b: bytes) (n: nat)
  : Lemma (requires array_repr t_repr esize xs b /\ n <= Seq.length xs)
          (ensures  esize * n <= len b /\
                    array_repr t_repr esize (Seq.slice xs 0 n) (slice b 0 (esize * n)) /\
                    array_repr t_repr esize (Seq.slice xs n (Seq.length xs))
                                            (slice b (esize * n) (len b)))
  = let m = Seq.length xs in
    M.lemma_mult_le_right esize n m;
    let pre = slice b 0 (esize * n) in
    let post = slice b (esize * n) (len b) in
    let aux_pre (i: nat) : Lemma (i < n ==> t_repr (Seq.index (Seq.slice xs 0 n) i)
                                                  (elem_bytes esize pre i)) =
      if i < n then elem_bytes_prefix esize b n i
    in
    Classical.forall_intro aux_pre;
    let aux_post (i: nat) : Lemma (i < m - n ==> t_repr (Seq.index (Seq.slice xs n m) i)
                                                       (elem_bytes esize post i)) =
      if i < m - n then begin
        elem_fits esize m (n + i);
        elem_bytes_suffix esize b n i
      end
    in
    Classical.forall_intro aux_post;
    M.distributivity_sub_right esize m n
#pop-options

#push-options "--z3rlimit 40"
let array_repr_join (#t: Type) (t_repr: t -> bytes -> prop) (esize: nat)
                    (xs ys: Seq.seq t) (b1 b2: bytes)
  : Lemma (requires array_repr t_repr esize xs b1 /\ array_repr t_repr esize ys b2)
          (ensures  array_repr t_repr esize (Seq.append xs ys) (append b1 b2))
  = let n = Seq.length xs in
    let m = Seq.length ys in
    let b = append b1 b2 in
    M.distributivity_add_right esize n m;
    let aux (i: nat) : Lemma (i < n + m ==> t_repr (Seq.index (Seq.append xs ys) i)
                                                  (elem_bytes esize b i)) =
      if i < n then begin
        elem_fits esize n i;
        Seq.lemma_append_len_disj b1 b2 b1 b2;
        Seq.slice_slice b 0 (len b1) (esize * i) (esize * i + esize);
        append_slice_left b1 b2
      end else if i < n + m then begin
        let j = i - n in
        elem_fits esize m j;
        M.distributivity_add_right esize n j;
        append_slice_right b1 b2;
        Seq.slice_slice b (len b1) (len b) (esize * j) (esize * j + esize)
      end
    in
    Classical.forall_intro aux
#pop-options

(* ---------------------------------------------------------------------------
   Ownership split and join

   `off` is passed in rather than computed as `esize * n` so that the caller
   supplies the `size_t` multiplication (and its overflow proof) at the point
   where it is known to fit; PAL always knows the offset statically.
   --------------------------------------------------------------------------- *)

ghost fn array_split (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t)
                     (#p: perm) (#xs: Seq.seq t)
                     (n: SZ.t { SZ.v n <= Seq.length xs })
                     (off: SZ.t { SZ.v off == SZ.v esize * SZ.v n })
  requires array_pts_to t_repr (SZ.v esize) a p xs
  ensures  array_pts_to t_repr (SZ.v esize) a p (Seq.slice xs 0 (SZ.v n))
  ensures  array_pts_to t_repr (SZ.v esize) (a +! off) p
                        (Seq.slice xs (SZ.v n) (Seq.length xs))
{
  unfold array_pts_to t_repr (SZ.v esize) a p xs;
  with b. assert (mem_pts_to a p b ** pure (array_repr t_repr (SZ.v esize) xs b));
  array_repr_split t_repr (SZ.v esize) xs b (SZ.v n);
  mem_split a off;
  fold array_pts_to t_repr (SZ.v esize) a p (Seq.slice xs 0 (SZ.v n));
  fold array_pts_to t_repr (SZ.v esize) (a +! off) p
                    (Seq.slice xs (SZ.v n) (Seq.length xs));
}

ghost fn array_join (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t)
                    (off: SZ.t) (#p: perm) (#xs #ys: Seq.seq t)
  requires array_pts_to t_repr (SZ.v esize) a p xs
  requires array_pts_to t_repr (SZ.v esize) (a +! off) p ys
  requires pure (SZ.v off == SZ.v esize * Seq.length xs)
  ensures  array_pts_to t_repr (SZ.v esize) a p (Seq.append xs ys)
{
  unfold array_pts_to t_repr (SZ.v esize) a p xs;
  with b1. assert (mem_pts_to a p b1 ** pure (array_repr t_repr (SZ.v esize) xs b1));
  unfold array_pts_to t_repr (SZ.v esize) (a +! off) p ys;
  with b2. assert (mem_pts_to (a +! off) p b2
                   ** pure (array_repr t_repr (SZ.v esize) ys b2));
  mem_join a #p #b1 #b2 off;
  array_repr_join t_repr (SZ.v esize) xs ys b1 b2;
  fold array_pts_to t_repr (SZ.v esize) a p (Seq.append xs ys);
}

(* ---------------------------------------------------------------------------
   Individual elements

   `elem_pts_to` is the generic shape of a layer-1 points-to: the concrete
   scalar predicates in `Pulse.Lib.C.Palow.Scalar` are definitionally equal to
   it (their representation happens to be unique, so they drop the
   existential), and a generated struct predicate is literally this.
   --------------------------------------------------------------------------- *)

let elem_pts_to (#t: Type0) (t_repr: t -> bytes -> prop)
                ([@@@mkey] a: ptr) (p: perm) (x: t) : slprop =
  exists* b. mem_pts_to a p b ** pure (t_repr x b)

let singleton_repr (#t: Type0) (t_repr: t -> bytes -> prop) (esize: nat) (x: t) (b: bytes)
  : Lemma (requires len b == esize /\ t_repr x b)
          (ensures  array_repr t_repr esize (Seq.create 1 x) b)
  = assert (elem_bytes esize b 0 == slice b 0 esize);
    Seq.lemma_eq_intro (slice b 0 esize) b

let singleton_repr_elim (#t: Type0) (t_repr: t -> bytes -> prop) (esize: nat) (x: t) (b: bytes)
  : Lemma (requires array_repr t_repr esize (Seq.create 1 x) b)
          (ensures  len b == esize /\ t_repr x b)
  = assert (elem_bytes esize b 0 == slice b 0 esize);
    Seq.lemma_eq_intro (slice b 0 esize) b

ghost fn array_singleton_elim (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t)
                              (#p: perm) (#x: t)
  requires array_pts_to t_repr (SZ.v esize) a p (Seq.create 1 x)
  ensures  elem_pts_to t_repr a p x
{
  unfold array_pts_to t_repr (SZ.v esize) a p (Seq.create 1 x);
  with b. assert (mem_pts_to a p b
                  ** pure (array_repr t_repr (SZ.v esize) (Seq.create 1 x) b));
  singleton_repr_elim t_repr (SZ.v esize) x b;
  fold elem_pts_to t_repr a p x;
}

ghost fn array_singleton_intro (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t)
                               (#p: perm) (#x: t)
  requires elem_pts_to t_repr a p x
  requires pure (forall (b: bytes). t_repr x b ==> len b == SZ.v esize)
  ensures  array_pts_to t_repr (SZ.v esize) a p (Seq.create 1 x)
{
  unfold elem_pts_to t_repr a p x;
  with b. assert (mem_pts_to a p b ** pure (t_repr x b));
  singleton_repr t_repr (SZ.v esize) x b;
  fold array_pts_to t_repr (SZ.v esize) a p (Seq.create 1 x);
}

(* ---------------------------------------------------------------------------
   Focusing on one element

   This is what `a[i]` needs, and it is two `array_split`s: the element lives at
   `a + esize * i`, exactly as C says. Nothing here is array-specific beyond the
   arithmetic -- the ownership transfer is `mem_split`.
   --------------------------------------------------------------------------- *)

ghost fn array_focus (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t)
                     (#p: perm) (#xs: Seq.seq t)
                     (i: SZ.t { SZ.v i < Seq.length xs })
                     (off: SZ.t { SZ.v off == SZ.v esize * SZ.v i })
  requires array_pts_to t_repr (SZ.v esize) a p xs
  ensures  array_pts_to t_repr (SZ.v esize) a p (Seq.slice xs 0 (SZ.v i))
  ensures  elem_pts_to t_repr (a +! off) p (Seq.index xs (SZ.v i))
  ensures  array_pts_to t_repr (SZ.v esize) ((a +! off) +! esize) p
                        (Seq.slice xs (SZ.v i + 1) (Seq.length xs))
{
  array_split t_repr a esize i off;
  let tail = Seq.slice xs (SZ.v i) (Seq.length xs);
  array_split t_repr (a +! off) esize #p #tail 1sz esize;
  Seq.lemma_eq_intro (Seq.slice tail 0 1) (Seq.create 1 (Seq.index xs (SZ.v i)));
  rewrite (array_pts_to t_repr (SZ.v esize) (a +! off) p (Seq.slice tail 0 1))
       as (array_pts_to t_repr (SZ.v esize) (a +! off) p
                        (Seq.create 1 (Seq.index xs (SZ.v i))));
  array_singleton_elim t_repr (a +! off) esize;
  Seq.lemma_eq_intro (Seq.slice tail 1 (Seq.length tail))
                     (Seq.slice xs (SZ.v i + 1) (Seq.length xs));
}
