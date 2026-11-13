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
module T = Pulse.Lib.C.Palow.Target
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

(* What an array's base address has to satisfy for every element of it to be
   correctly aligned. The divisibility is the well-formedness of the pair
   (stride, alignment): C guarantees `alignof(T)` divides `sizeof(T)`, which is
   what makes element `i` aligned whenever the base is. C's power-of-two
   alignments also divide the pointer-word modulus. Carrying these inside the
   predicate rather than demanding it at each use means a split, a focus and a
   `+! esize` all preserve alignment without anyone restating it. *)
(* Same shape as `aligned`, and opaque for the same reason: the divisibility
   of the address is hidden behind `divides_addr` so that a proof carrying many
   of these facts at once does not hand Z3 a pile of nonlinear arithmetic. *)
let array_aligned (esize: nat) (ealign: nat) (a: ptr) : prop =
  esize > 0 /\ ealign > 0 /\ esize % ealign == 0 /\
  pow2 32 % ealign == 0 /\ divides_addr a ealign

let array_aligned_add (esize: nat) (ealign: nat) (a: ptr) (n: SZ.t)
  : Lemma (requires array_aligned esize ealign a /\ SZ.v n % esize == 0)
          (ensures  array_aligned esize ealign (a +! n))
  = reveal_opaque (`%divides_addr) divides_addr;
    FStar.Math.Lemmas.lemma_div_exact (SZ.v n) esize;
    FStar.Math.Lemmas.lemma_div_exact esize ealign;
    FStar.Math.Lemmas.paren_mul_right (SZ.v n / esize) (esize / ealign) ealign;
    FStar.Math.Lemmas.multiple_modulo_lemma ((SZ.v n / esize) * (esize / ealign)) ealign;
    divides_addr_add a ealign n

(* The form every split actually has: the offset is a whole number of
   elements. *)
let array_aligned_step (esize: nat) (ealign: nat) (a: ptr) (n: SZ.t) (k: nat)
  : Lemma (requires array_aligned esize ealign a /\ SZ.v n == esize * k)
          (ensures  array_aligned esize ealign (a +! n))
  = FStar.Math.Lemmas.swap_mul esize k;
    FStar.Math.Lemmas.multiple_modulo_lemma k esize;
    array_aligned_add esize ealign a n

let array_pts_to (#t: Type) (t_repr: t -> bytes -> prop) (esize: nat) (ealign: nat)
                 ([@@@mkey] a: ptr) (p: perm) (xs: Seq.seq t) : slprop =
  exists* b. mem_pts_to a p b
             ** pure (array_repr t_repr esize xs b /\ array_aligned esize ealign a)

(* Giving a read-only share of literal storage back. Literal storage is
   static and nobody owns it, so a share of it is simply dropped; this is
   proved, not assumed.

   Acquiring one is *not* here. It would have to read `t_repr`, `esize` and
   `ealign` as parameters, and a trusted function that produces
   `array_pts_to t_repr ...` for a `t_repr` of the caller's choosing is false:
   instantiate it with a relation no byte string satisfies and `array_repr`
   -- which conjoins `t_repr` at every element -- is `False`, so the
   postcondition yields `pure False` from `emp`. A `_ghost_stmt` can say that
   in C. The acquisition is therefore emitted per literal, with the element
   type's own representation written in, next to the function that uses it:
   each such assumption is a statement about one piece of static data, in the
   same way an immutable global's `acquire_var_*` is. *)
ghost fn literal_share_drop (#t: Type0) (t_repr: t -> bytes -> prop)
                            (esize: SZ.t) (ealign: SZ.t) (xs: list t)
  requires exists* p. array_pts_to t_repr (SZ.v esize) (SZ.v ealign)
             (literal_addr xs) p (Pulse.Lib.C.Palow.ConstSeq.const_seq xs)
  ensures  emp
{
  drop_ (exists* p. array_pts_to t_repr (SZ.v esize) (SZ.v ealign)
           (literal_addr xs) p (Pulse.Lib.C.Palow.ConstSeq.const_seq xs))
}

(* The two directions between an array's ownership and the bytes under it.
   Every scalar type publishes this pair under its own name, and a union arm
   or a structure field has to be able to ask for it without knowing which
   kind of thing it is holding. `array_pts_to` is a definition, so both are
   a fold. *)
ghost fn array_conceal (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                       (#p: perm) (#b: bytes) (#xs: Seq.seq t)
  requires mem_pts_to a p b
  requires pure (array_repr t_repr (SZ.v esize) xs b)
  requires pure (array_aligned (SZ.v esize) (SZ.v ealign) a)
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
{
  fold (array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs);
}

ghost fn array_reveal (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                      (#p: perm) (#xs: Seq.seq t)
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  ensures  exists* b. mem_pts_to a p b ** pure (array_repr t_repr (SZ.v esize) xs b)
{
  unfold (array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs);
}

(* The same pair, with the representation kept out of the solver's sight.
   `array_repr` is a quantifier over the elements, and a proof that only
   carves an enclosing object into pieces -- a structure's byte-level view,
   with an array field among the pieces -- needs nothing from it but the
   length. Unfolded there it is pure cost, and enough of it times the proof
   out. So the byte-level view of a structure states its array fields with
   `array_repr_o`, and these two are the only places it is opened. *)
[@@"opaque_to_smt"]
let array_repr_o (#t: Type) (t_repr: t -> bytes -> prop) (esize: nat)
                 (xs: Seq.seq t) (b: bytes) : prop =
  array_repr t_repr esize xs b

let array_repr_o_eq (#t: Type) (t_repr: t -> bytes -> prop) (esize: nat)
                    (xs: Seq.seq t) (b: bytes)
  : Lemma (array_repr_o t_repr esize xs b <==> array_repr t_repr esize xs b)
  = reveal_opaque (`%array_repr_o) (array_repr_o t_repr esize xs b)

ghost fn array_conceal_o (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                         (#p: perm) (#b: bytes) (#xs: Seq.seq t)
  requires mem_pts_to a p b
  requires pure (array_repr_o t_repr (SZ.v esize) xs b)
  requires pure (array_aligned (SZ.v esize) (SZ.v ealign) a)
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
{
  array_repr_o_eq t_repr (SZ.v esize) xs b;
  fold (array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs);
}

ghost fn array_reveal_o (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                        (#p: perm) (#xs: Seq.seq t)
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  ensures  exists* b. mem_pts_to a p b **
                      pure (array_repr_o t_repr (SZ.v esize) xs b /\
                            len b == SZ.v esize * Seq.length xs)
{
  unfold (array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs);
  with b. assert (mem_pts_to a p b);
  array_repr_o_eq t_repr (SZ.v esize) xs b;
  assert pure (array_repr t_repr (SZ.v esize) xs b);
  assert pure (array_repr_o t_repr (SZ.v esize) xs b);
}

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

ghost fn array_split (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                     (#p: perm) (#xs: Seq.seq t)
                     (n: SZ.t { SZ.v n <= Seq.length xs })
                     (off: SZ.t { SZ.v off == SZ.v esize * SZ.v n })
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p (Seq.slice xs 0 (SZ.v n))
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) (a +! off) p
                        (Seq.slice xs (SZ.v n) (Seq.length xs))
  ensures  pure (array_aligned (SZ.v esize) (SZ.v ealign) (a +! off))
{
  unfold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs;
  with b. assert (mem_pts_to a p b ** pure (array_repr t_repr (SZ.v esize) xs b));
  array_repr_split t_repr (SZ.v esize) xs b (SZ.v n);
  array_aligned_step (SZ.v esize) (SZ.v ealign) a off (SZ.v n);
  mem_split a off;
  fold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p (Seq.slice xs 0 (SZ.v n));
  fold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) (a +! off) p
                    (Seq.slice xs (SZ.v n) (Seq.length xs));
}

ghost fn array_join (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                    (off: SZ.t) (#p: perm) (#xs #ys: Seq.seq t)
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) (a +! off) p ys
  requires pure (SZ.v off == SZ.v esize * Seq.length xs)
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p (Seq.append xs ys)
{
  unfold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs;
  with b1. assert (mem_pts_to a p b1 ** pure (array_repr t_repr (SZ.v esize) xs b1));
  unfold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) (a +! off) p ys;
  with b2. assert (mem_pts_to (a +! off) p b2
                   ** pure (array_repr t_repr (SZ.v esize) ys b2));
  mem_join a #p #b1 #b2 off;
  array_repr_join t_repr (SZ.v esize) xs ys b1 b2;
  fold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p (Seq.append xs ys);
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

ghost fn array_singleton_elim (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                              (#p: perm) (#x: t)
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p (Seq.create 1 x)
  ensures  elem_pts_to t_repr a p x
{
  unfold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p (Seq.create 1 x);
  with b. assert (mem_pts_to a p b
                  ** pure (array_repr t_repr (SZ.v esize) (Seq.create 1 x) b));
  singleton_repr_elim t_repr (SZ.v esize) x b;
  fold elem_pts_to t_repr a p x;
}

ghost fn array_singleton_intro (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                               (#p: perm) (#x: t)
  requires elem_pts_to t_repr a p x
  requires pure (forall (b: bytes). t_repr x b ==> len b == SZ.v esize)
  requires pure (array_aligned (SZ.v esize) (SZ.v ealign) a)
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p (Seq.create 1 x)
{
  unfold elem_pts_to t_repr a p x;
  with b. assert (mem_pts_to a p b ** pure (t_repr x b));
  singleton_repr t_repr (SZ.v esize) x b;
  fold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p (Seq.create 1 x);
}

(* ---------------------------------------------------------------------------
   Focusing on one element

   This is what `a[i]` needs, and it is two `array_split`s: the element lives at
   `a + esize * i`, exactly as C says. Nothing here is array-specific beyond the
   arithmetic -- the ownership transfer is `mem_split`.
   --------------------------------------------------------------------------- *)

ghost fn array_focus (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                     (#p: perm) (#xs: Seq.seq t)
                     (i: SZ.t { SZ.v i < Seq.length xs })
                     (off: SZ.t { SZ.v off == SZ.v esize * SZ.v i })
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p (Seq.slice xs 0 (SZ.v i))
  ensures  elem_pts_to t_repr (a +! off) p (Seq.index xs (SZ.v i))
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) ((a +! off) +! esize) p
                        (Seq.slice xs (SZ.v i + 1) (Seq.length xs))
  ensures  pure (array_aligned (SZ.v esize) (SZ.v ealign) (a +! off))
{
  array_split t_repr a esize ealign i off;
  let tail = Seq.slice xs (SZ.v i) (Seq.length xs);
  array_split t_repr (a +! off) esize ealign #p #tail 1sz esize;
  Seq.lemma_eq_intro (Seq.slice tail 0 1) (Seq.create 1 (Seq.index xs (SZ.v i)));
  rewrite (array_pts_to t_repr (SZ.v esize) (SZ.v ealign) (a +! off) p (Seq.slice tail 0 1))
       as (array_pts_to t_repr (SZ.v esize) (SZ.v ealign) (a +! off) p
                        (Seq.create 1 (Seq.index xs (SZ.v i))));
  array_singleton_elim t_repr (a +! off) esize ealign;
  Seq.lemma_eq_intro (Seq.slice tail 1 (Seq.length tail))
                     (Seq.slice xs (SZ.v i + 1) (Seq.length xs));
}

(* ---------------------------------------------------------------------------
   Putting the element back

   `array_focus` on its own is only half of `a[i]`: a read has to give the
   element back unchanged and a write has to give a different one back, and
   both are this. Taking the new element as an implicit `y` rather than
   insisting it is `Seq.index xs i` is what makes the write case work, and the
   read case is `y == Seq.index xs i`, where `Seq.upd` is the identity.

   The side condition is the one place where a representation relation has to
   be a *function* of the value's width: putting `y` back into an array whose
   stride is `esize` is only meaningful if `y`'s bytes are `esize` long. Every
   `t_repr` PAL generates satisfies it -- that is what `t_repr_len` says --
   and it is stated rather than assumed because `elem_pts_to` alone does not
   know the stride.
   --------------------------------------------------------------------------- *)

let upd_split (#t: Type) (xs: Seq.seq t) (i: nat { i < Seq.length xs }) (y: t)
  : Lemma (Seq.upd xs i y
           == Seq.append (Seq.slice xs 0 i)
                         (Seq.append (Seq.create 1 y)
                                     (Seq.slice xs (i + 1) (Seq.length xs))))
  = Seq.lemma_eq_intro (Seq.upd xs i y)
                       (Seq.append (Seq.slice xs 0 i)
                                   (Seq.append (Seq.create 1 y)
                                               (Seq.slice xs (i + 1) (Seq.length xs))))

ghost fn array_unfocus (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                       (#p: perm) (#xs: Seq.seq t) (#y: t)
                       (i: SZ.t { SZ.v i < Seq.length xs })
                       (off: SZ.t { SZ.v off == SZ.v esize * SZ.v i })
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p (Seq.slice xs 0 (SZ.v i))
  requires elem_pts_to t_repr (a +! off) p y
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) ((a +! off) +! esize) p
                        (Seq.slice xs (SZ.v i + 1) (Seq.length xs))
  requires pure (forall (b: bytes). t_repr y b ==> len b == SZ.v esize)
  requires pure (array_aligned (SZ.v esize) (SZ.v ealign) (a +! off))
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p (Seq.upd xs (SZ.v i) y)
{
  array_singleton_intro t_repr (a +! off) esize ealign;
  array_join t_repr (a +! off) esize ealign esize
             #p #(Seq.create 1 y) #(Seq.slice xs (SZ.v i + 1) (Seq.length xs));
  array_join t_repr a esize ealign off
             #p #(Seq.slice xs 0 (SZ.v i))
             #(Seq.append (Seq.create 1 y) (Seq.slice xs (SZ.v i + 1) (Seq.length xs)));
  upd_split xs (SZ.v i) y;
  rewrite (array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p
                        (Seq.append (Seq.slice xs 0 (SZ.v i))
                                    (Seq.append (Seq.create 1 y)
                                                (Seq.slice xs (SZ.v i + 1) (Seq.length xs)))))
       as (array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p (Seq.upd xs (SZ.v i) y));
}

(* The generic layer-1 view of one element, opened and closed. A scalar's own
   `t_reveal`/`t_conceal` produce and consume exactly this shape, so these two
   are the adapters between an array element and the machine operations. *)

ghost fn elem_reveal (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (#p: perm) (#x: t)
  requires elem_pts_to t_repr a p x
  ensures  exists* b. mem_pts_to a p b ** pure (t_repr x b)
{
  unfold elem_pts_to t_repr a p x;
}

ghost fn elem_conceal (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr)
                      (#p: perm) (#b: bytes) (#x: t)
  requires mem_pts_to a p b
  requires pure (t_repr x b)
  ensures  elem_pts_to t_repr a p x
{
  fold elem_pts_to t_repr a p x;
}

(* Closing a focus that only read: the sequence that comes back is the one that
   went in. This is `array_unfocus` plus the observation that `Seq.upd xs i
   (Seq.index xs i)` is `xs`, done once here so that every emitted subscript
   read does not have to repeat it. *)
ghost fn array_unfocus_read (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                            (#p: perm) (#xs: Seq.seq t)
                            (i: SZ.t { SZ.v i < Seq.length xs })
                            (off: SZ.t { SZ.v off == SZ.v esize * SZ.v i })
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p (Seq.slice xs 0 (SZ.v i))
  requires elem_pts_to t_repr (a +! off) p (Seq.index xs (SZ.v i))
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) ((a +! off) +! esize) p
                        (Seq.slice xs (SZ.v i + 1) (Seq.length xs))
  requires pure (forall (b: bytes).
                   t_repr (Seq.index xs (SZ.v i)) b ==> len b == SZ.v esize)
  requires pure (array_aligned (SZ.v esize) (SZ.v ealign) (a +! off))
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
{
  array_unfocus t_repr a esize ealign i off;
  Seq.lemma_eq_intro (Seq.upd xs (SZ.v i) (Seq.index xs (SZ.v i))) xs;
  rewrite (array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p (Seq.upd xs (SZ.v i) (Seq.index xs (SZ.v i))))
       as (array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs);
}

ghost fn array_fits (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                    (#p: perm) (#xs: Seq.seq t)
  preserves array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  ensures   pure (SZ.fits (addr_of a + SZ.v esize * Seq.length xs) /\
                  addr_of a + SZ.v esize * Seq.length xs < T.addr_limit)
{
  unfold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs;
  with b. assert (mem_pts_to a p b ** pure (array_repr t_repr (SZ.v esize) xs b));
  mem_pts_to_fits a;
  fold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs;
}

(* The byte offset of an in-bounds element fits in a `size_t`, so the
   multiplication a subscript needs is well-defined. This is not an extra
   assumption: owning the array means owning `esize * length xs` bytes at `a`,
   and `mem_pts_to_fits` says a live range ends at an address that fits. C says
   the same thing, and for the same reason. *)
ghost fn array_offset_fits (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                           (#p: perm) (#xs: Seq.seq t)
                           (i: SZ.t { SZ.v i < Seq.length xs })
  preserves array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  ensures   pure (SZ.fits (SZ.v esize * SZ.v i))
  ensures   pure (addr_of a + SZ.v esize * Seq.length xs < T.addr_limit)
{
  array_fits t_repr a esize ealign;
  elem_fits (SZ.v esize) (Seq.length xs) (SZ.v i);
  SZ.fits_lte (SZ.v esize * SZ.v i) (addr_of a + SZ.v esize * Seq.length xs);
}

(* ---------------------------------------------------------------------------
   Walking a pointer through an array

   `for (; *s; s++)` never indexes the array it reads: it moves `s` itself.
   The ownership stays where the contract put it, at the array's base `a`, and
   `s` is just some pointer into it. What makes `*s` an element of that array
   is three facts about `s` relative to `a`: the same provenance (it was formed
   from `a` by `+!` and `-!`, which keep provenance), an address at or above
   `a`'s, and an offset that is a whole number of elements. `walk_ok` is those
   three, and `walk_idx` is the element `s` is at. Neither says `s` is in
   bounds -- one past the end is a pointer C lets a loop stop at -- so the
   element access asks for that separately.

   Both survive a step of `esize` that does not wrap, which is what lets a loop
   carry them: the emitter states `walk_ok` in every invariant for every
   pointer it walks, and the bounds are the invariant the source writes.
   --------------------------------------------------------------------------- *)

let walk_ok (esize: nat) (a q: ptr) : prop =
  esize > 0 /\ prov_of q == prov_of a /\ addr_of a <= addr_of q /\
  (addr_of q - addr_of a) % esize == 0

let walk_idx (esize: nat) (a q: ptr) : GTot int =
  if esize > 0 then (addr_of q - addr_of a) / esize else 0

(* The position as a `size_t`, wherever it is one. A contract that says
   `_exists(size_t i, ...)` of where a walked pointer stopped needs a
   `SizeT.t` the solver can offer as the witness, and the position itself is
   only an `int`; mentioning the position puts this term next to it. *)
let walk_size (esize: nat) (a q: ptr) : GTot SZ.t =
  let i = walk_idx esize a q in
  if FStar.IndefiniteDescription.strong_excluded_middle (0 <= i /\ SZ.fits i)
  then SZ.uint_to_t i
  else 0sz

let walk_size_v (esize: nat) (a q: ptr)
  : Lemma (0 <= walk_idx esize a q /\ SZ.fits (walk_idx esize a q) ==>
           SZ.v (walk_size esize a q) == walk_idx esize a q)
          [SMTPat (walk_idx esize a q)]
  = ()

let walk_addr (esize: nat) (a q: ptr) (i: nat)
  : Lemma (requires walk_ok esize a q)
          (ensures  addr_of q + esize * i == addr_of a + esize * (walk_idx esize a q + i))
  = M.euclidean_division_definition (addr_of q - addr_of a) esize;
    M.distributivity_add_right esize (walk_idx esize a q) i

(* The base, offset to the element `q[i]` stands for, is `q +! off`: the same
   provenance and, because the owned range does not reach `addr_limit`, the
   same address without wrapping on either side. *)
let walk_same (esize: nat) (a q: ptr) (n: nat) (i: nat) (off offj: SZ.t)
  : Lemma (requires walk_ok esize a q /\ walk_idx esize a q + i < n /\
                    addr_of a + esize * n < T.addr_limit /\
                    SZ.v off == esize * i /\ SZ.v offj == esize * (walk_idx esize a q + i))
          (ensures  a +! offj == q +! off)
  = walk_addr esize a q i;
    elem_fits esize n (walk_idx esize a q + i);
    addr_of_add_nowrap a offj;
    addr_of_add_nowrap q off;
    ptr_ext (a +! offj) (q +! off)

ghost fn array_offset_fits_at (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                              (q: ptr) (#p: perm) (#xs: Seq.seq t) (i: SZ.t { walk_ok (SZ.v esize) a q /\ walk_idx (SZ.v esize) a q + SZ.v i < Seq.length xs })
  preserves array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  ensures   pure (SZ.fits (SZ.v esize * SZ.v i))
{
  array_fits t_repr a esize ealign;
  let w : erased nat = walk_idx (SZ.v esize) a q;
  elem_fits (SZ.v esize) (Seq.length xs) (w + SZ.v i);
  M.distributivity_add_right (SZ.v esize) w (SZ.v i);
  SZ.fits_lte (SZ.v esize * SZ.v i) (addr_of a + SZ.v esize * Seq.length xs);
}

ghost fn array_focus_at (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                        (q: ptr) (#p: perm) (#xs: Seq.seq t)
                        (i: SZ.t { walk_ok (SZ.v esize) a q /\ walk_idx (SZ.v esize) a q + SZ.v i < Seq.length xs })
                        (off: SZ.t { SZ.v off == SZ.v esize * SZ.v i })
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p
                        (Seq.slice xs 0 (walk_idx (SZ.v esize) a q + SZ.v i))
  ensures  elem_pts_to t_repr (q +! off) p (Seq.index xs (walk_idx (SZ.v esize) a q + SZ.v i))
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) ((q +! off) +! esize) p
                        (Seq.slice xs (walk_idx (SZ.v esize) a q + SZ.v i + 1) (Seq.length xs))
  ensures  pure (array_aligned (SZ.v esize) (SZ.v ealign) (q +! off))
  ensures  pure (SZ.fits (addr_of a + SZ.v esize * Seq.length xs) /\
                 addr_of a + SZ.v esize * Seq.length xs < T.addr_limit)
{
  array_fits t_repr a esize ealign;
  let w : erased nat = walk_idx (SZ.v esize) a q;
  elem_fits (SZ.v esize) (Seq.length xs) (w + SZ.v i);
  M.lemma_mult_le_right (SZ.v esize) 1 (Seq.length xs);
  SZ.fits_lte (w + SZ.v i) (addr_of a + SZ.v esize * Seq.length xs);
  SZ.fits_lte (SZ.v esize * (w + SZ.v i)) (addr_of a + SZ.v esize * Seq.length xs);
  let j = SZ.uint_to_t (w + SZ.v i);
  let offj = SZ.uint_to_t (SZ.v esize * (w + SZ.v i));
  walk_same (SZ.v esize) a q (Seq.length xs) (SZ.v i) off offj;
  array_focus t_repr a esize ealign j offj;
  rewrite each (a +! offj) as (q +! off);
}

ghost fn array_unfocus_at (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                          (q: ptr) (#p: perm) (#xs: Seq.seq t) (#y: t)
                          (i: SZ.t { walk_ok (SZ.v esize) a q /\ walk_idx (SZ.v esize) a q + SZ.v i < Seq.length xs })
                          (off: SZ.t { SZ.v off == SZ.v esize * SZ.v i })
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p
                        (Seq.slice xs 0 (walk_idx (SZ.v esize) a q + SZ.v i))
  requires elem_pts_to t_repr (q +! off) p y
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) ((q +! off) +! esize) p
                        (Seq.slice xs (walk_idx (SZ.v esize) a q + SZ.v i + 1) (Seq.length xs))
  requires pure (forall (b: bytes). t_repr y b ==> len b == SZ.v esize)
  requires pure (array_aligned (SZ.v esize) (SZ.v ealign) (q +! off))
  requires pure (SZ.fits (addr_of a + SZ.v esize * Seq.length xs) /\
                 addr_of a + SZ.v esize * Seq.length xs < T.addr_limit)
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p
                        (Seq.upd xs (walk_idx (SZ.v esize) a q + SZ.v i) y)
{
  let w : erased nat = walk_idx (SZ.v esize) a q;
  elem_fits (SZ.v esize) (Seq.length xs) (w + SZ.v i);
  M.lemma_mult_le_right (SZ.v esize) 1 (Seq.length xs);
  SZ.fits_lte (w + SZ.v i) (addr_of a + SZ.v esize * Seq.length xs);
  SZ.fits_lte (SZ.v esize * (w + SZ.v i)) (addr_of a + SZ.v esize * Seq.length xs);
  let j = SZ.uint_to_t (w + SZ.v i);
  let offj = SZ.uint_to_t (SZ.v esize * (w + SZ.v i));
  walk_same (SZ.v esize) a q (Seq.length xs) (SZ.v i) off offj;
  rewrite each (q +! off) as (a +! offj);
  array_unfocus t_repr a esize ealign #p #xs #y j offj;
}

ghost fn array_unfocus_read_at (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                               (q: ptr) (#p: perm) (#xs: Seq.seq t)
                               (i: SZ.t { walk_ok (SZ.v esize) a q /\ walk_idx (SZ.v esize) a q + SZ.v i < Seq.length xs })
                               (off: SZ.t { SZ.v off == SZ.v esize * SZ.v i })
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p
                        (Seq.slice xs 0 (walk_idx (SZ.v esize) a q + SZ.v i))
  requires elem_pts_to t_repr (q +! off) p (Seq.index xs (walk_idx (SZ.v esize) a q + SZ.v i))
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) ((q +! off) +! esize) p
                        (Seq.slice xs (walk_idx (SZ.v esize) a q + SZ.v i + 1) (Seq.length xs))
  requires pure (forall (b: bytes).
                   t_repr (Seq.index xs (walk_idx (SZ.v esize) a q + SZ.v i)) b ==> len b == SZ.v esize)
  requires pure (array_aligned (SZ.v esize) (SZ.v ealign) (q +! off))
  requires pure (SZ.fits (addr_of a + SZ.v esize * Seq.length xs) /\
                 addr_of a + SZ.v esize * Seq.length xs < T.addr_limit)
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
{
  array_unfocus_at t_repr a esize ealign q #p #xs i off;
  Seq.lemma_eq_intro (Seq.upd xs (walk_idx (SZ.v esize) a q + SZ.v i)
                              (Seq.index xs (walk_idx (SZ.v esize) a q + SZ.v i))) xs;
  rewrite (array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p
                        (Seq.upd xs (walk_idx (SZ.v esize) a q + SZ.v i)
                                 (Seq.index xs (walk_idx (SZ.v esize) a q + SZ.v i))))
       as (array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs);
}

(* A step back keeps the provenance and moves the address. `addr_of_sub` says
   so, but is triggered on an `addr_of` that a `walk_ok` on `q -! n` only
   mentions after unfolding; this is the same fact triggered on the step. *)
let walk_sub (q: ptr) (n: SZ.t { SZ.v n <= addr_of q })
  : Lemma (addr_of (q -! n) == addr_of q - SZ.v n /\ prov_of (q -! n) == prov_of q)
          [SMTPat (q -! n)]
  = addr_of_sub q n

(* A walked pointer is the base plus its byte offset, which is how a contract
   that names a position in the array as `a + i` recognises it. *)
let walk_is_add (esize: nat) (a q: ptr)
  : Lemma (requires walk_ok esize a q)
          (ensures  SZ.fits (addr_of q - addr_of a) ==>
                    q == a +! SZ.uint_to_t (addr_of q - addr_of a))
          [SMTPat (walk_ok esize a q)]
  = if SZ.fits (addr_of q - addr_of a) then begin
      let d = SZ.uint_to_t (addr_of q - addr_of a) in
      addr_of_add_nowrap a d;
      ptr_ext (a +! d) q
    end

(* `a + i` in a contract, for an array of `esize`-byte elements and a
   computed `i`: the pointer `i` elements past `a`. Total, so that a contract
   can name it without first proving the offset fits; where it does not, the
   value is `a` itself and nothing can be concluded about it. *)
let elem_ptr (esize: nat) (a: ptr) (i: SZ.t) : GTot ptr =
  if FStar.IndefiniteDescription.strong_excluded_middle
       (SZ.fits (esize * SZ.v i) /\ addr_of a + esize * SZ.v i < T.addr_limit)
  then a +! SZ.uint_to_t (esize * SZ.v i)
  else a

(* A pointer a callee returned as `a + i` is a walk through `a`, at `i`. *)
let elem_ptr_walk (esize: pos) (a: ptr) (i: SZ.t)
  : Lemma (walk_ok esize a (elem_ptr esize a i) /\
           ((SZ.fits (esize * SZ.v i) /\ addr_of a + esize * SZ.v i < T.addr_limit) ==>
            (addr_of (elem_ptr esize a i) == addr_of a + esize * SZ.v i /\
             walk_idx esize a (elem_ptr esize a i) == SZ.v i)))
          [SMTPat (elem_ptr esize a i)]
  = if FStar.IndefiniteDescription.strong_excluded_middle
       (SZ.fits (esize * SZ.v i) /\ addr_of a + esize * SZ.v i < T.addr_limit)
    then begin
      addr_of_add_nowrap a (SZ.uint_to_t (esize * SZ.v i));
      M.cancel_mul_mod (SZ.v i) esize;
      M.cancel_mul_div (SZ.v i) esize
    end

(* And a walked pointer is `a + i` at its position, which is the witness a
   contract's `_exists(size_t i, return == a + i ...)` needs. *)
let walk_is_elem (esize: nat) (a q: ptr)
  : Lemma (requires walk_ok esize a q)
          (ensures  SZ.fits (addr_of q - addr_of a) ==>
                    q == elem_ptr esize a (walk_size esize a q))
          [SMTPat (walk_ok esize a q)]
  = if SZ.fits (addr_of q - addr_of a) then begin
      let d = addr_of q - addr_of a in
      M.euclidean_division_definition d esize;
      SZ.fits_lte (d / esize) d;
      addr_bound q;
      addr_of_add_nowrap a (SZ.uint_to_t d);
      ptr_ext (a +! SZ.uint_to_t d) q
    end

(* ---------------------------------------------------------------------------
   Storage that is not yet initialised

   A C array local is `esize * n` bytes of automatic storage whose elements are
   written one at a time, so at any point some hold a value and some do not.
   The way to say that here is not a new predicate but a different
   representation relation: an element is an `option t`, and `None` represents
   any bytes of the right width.

   Everything above then applies unchanged, because none of it looks at the
   representation. `array_split`, `array_join`, `array_focus` and
   `array_unfocus` work on a partially initialised array exactly as they do on
   a fully initialised one, and allocating one is a single proof rather than an
   unrolling per length.

   The payoff is where the initialisation is tracked. Reading `a[i]` needs
   `Some? (Seq.index xs i)`, which is C's rule that reading an uninitialised
   object is undefined -- and it is a proof obligation on the generated code
   rather than a translator refusal, so the emitter does not have to remember
   which elements have been written. The sequence remembers.
   --------------------------------------------------------------------------- *)

let maybe_repr (#t: Type0) (t_repr: t -> bytes -> prop) (esize: nat)
               (x: option t) (b: bytes) : prop =
  match x with
  | None -> len b == esize
  | Some v -> t_repr v b

let create_repr (#t: Type0) (t_repr: t -> bytes -> prop) (esize: nat) (n: nat) (b: bytes)
  : Lemma (requires len b == esize * n)
          (ensures  array_repr (maybe_repr t_repr esize) esize
                               (Seq.create n (None #t)) b)
  = let xs : Seq.seq (option t) = Seq.create n None in
    let aux (i: nat)
      : Lemma (i < n ==> maybe_repr t_repr esize (Seq.index xs i) (elem_bytes esize b i))
      = if i < n then elem_fits esize n i
    in
    Classical.forall_intro aux

(* Claim `esize * n` raw bytes as an array of uninitialised elements. This is
   the only place the two views meet, and it is a fold: the bytes are already
   the right length, and `None` represents any bytes of that length. *)
ghost fn array_claim_uninit (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr)
                            (esize: SZ.t) (ealign: SZ.t) (n: SZ.t) (#b: bytes)
  requires mem_pts_to a 1.0R b
  requires pure (len b == SZ.v esize * SZ.v n)
  requires pure (array_aligned (SZ.v esize) (SZ.v ealign) a)
  ensures  array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) (SZ.v ealign) a 1.0R
                        (Seq.create (SZ.v n) (None #t))
{
  create_repr t_repr (SZ.v esize) (SZ.v n) b;
  fold array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) (SZ.v ealign) a 1.0R
                    (Seq.create (SZ.v n) (None #t));
}

(* Every element of a zeroed block is itself zeroed: slicing a constant
   sequence anywhere gives the same constant sequence. *)
let elem_bytes_zeroed (esize: nat) (n: nat) (i: nat)
  : Lemma (requires i < n)
          (ensures  elem_bytes esize (zeroed (esize * n)) i == zeroed esize)
  = elem_fits esize n i;
    Seq.lemma_eq_elim (elem_bytes esize (zeroed (esize * n)) i) (zeroed esize)

(* Claim `esize * n` zeroed bytes as an array of *initialised* elements.
   `calloc` differs from `malloc` in exactly this: the storage arrives holding
   a value, so the caller is handed `Some z` rather than `None` and may read
   before writing.

   Which value `z` is cannot be decided here -- it is whatever the element
   type's representation relation makes of an all-zero range -- so it is an
   implicit the caller fixes, with `t_repr z (zeroed esize)` as the obligation
   that it really is the one. *)
ghost fn array_claim_zeroed (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr)
                            (esize: SZ.t) (ealign: SZ.t) (n: SZ.t) (#z: t) (#b: bytes)
  requires mem_pts_to a 1.0R b
  requires pure (b == zeroed (SZ.v esize * SZ.v n))
  requires pure (t_repr z (zeroed (SZ.v esize)))
  requires pure (array_aligned (SZ.v esize) (SZ.v ealign) a)
  ensures  array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) (SZ.v ealign) a 1.0R
                        (Seq.create (SZ.v n) (Some z))
{
  Classical.forall_intro (Classical.move_requires (elem_bytes_zeroed (SZ.v esize) (SZ.v n)));
  fold array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) (SZ.v ealign) a 1.0R
                    (Seq.create (SZ.v n) (Some z));
}

(* And back, at whatever the elements have become. Giving the storage up does
   not depend on what was last written to it, which is why this asks for no
   `Some`. *)
ghost fn array_forget (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                      (#xs: Seq.seq (option t))
  requires array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) (SZ.v ealign) a 1.0R xs
  ensures  exists* b. mem_pts_to a 1.0R b
                      ** pure (len b == SZ.v esize * Seq.length xs)
{
  unfold array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) (SZ.v ealign) a 1.0R xs;
}

(* An element that does hold a value, as an ordinary element of `t`. The
   `Some?` is stated as a side condition rather than matched on the implicit,
   because at the point of use what is in context is `Seq.index xs i` and only
   the solver knows it is a `Some`. *)
ghost fn elem_maybe_get (#t: Type0) (t_repr: t -> bytes -> prop) (esize: SZ.t) (a: ptr)
                        (#p: perm) (#x: (x: option t { Some? x }))
  requires elem_pts_to (maybe_repr t_repr (SZ.v esize)) a p x
  ensures  elem_pts_to t_repr a p (Some?.v x)
{
  unfold elem_pts_to (maybe_repr t_repr (SZ.v esize)) a p x;
  fold elem_pts_to t_repr a p (Some?.v x);
}

ghost fn elem_maybe_put (#t: Type0) (t_repr: t -> bytes -> prop) (esize: SZ.t) (a: ptr)
                        (#p: perm) (#x: t)
  requires elem_pts_to t_repr a p x
  ensures  elem_pts_to (maybe_repr t_repr (SZ.v esize)) a p (Some x)
{
  unfold elem_pts_to t_repr a p x;
  fold elem_pts_to (maybe_repr t_repr (SZ.v esize)) a p (Some x);
}

(* The write-only view of one element, whatever it held before. A write to
   `a[i]` goes down to this and comes back up through the type's own
   `t_write_uninit`, which is the same path a scalar local takes. *)
ghost fn elem_maybe_reveal (#t: Type0) (t_repr: t -> bytes -> prop) (esize: SZ.t) (a: ptr)
                           (#x: option t)
  requires elem_pts_to (maybe_repr t_repr (SZ.v esize)) a 1.0R x
  requires pure (forall (v: t) (b: bytes). t_repr v b ==> len b == SZ.v esize)
  ensures  exists* b. mem_pts_to a 1.0R b ** pure (len b == SZ.v esize)
{
  unfold elem_pts_to (maybe_repr t_repr (SZ.v esize)) a 1.0R x;
}

(* ---------------------------------------------------------------------------
   An array's storage, as one predicate

   `T f[N]` inside a structure is N elements of storage, and a structure's
   write-only view has to name that storage without naming what is in it --
   there is nothing in it. Hiding the sequence is what makes the view a
   *predicate on the address alone*, which is what every other field's
   `_pts_to_uninit` already is, and it is what lets the struct-level fold that
   assembles them stay a fold.

   The length stays visible because it is the one thing the storage does
   determine: `N` is part of the field's type. *)
let array_pts_to_uninit (#t: Type0) (t_repr: t -> bytes -> prop)
                        (esize: nat) (ealign: nat) (n: nat) ([@@@mkey] a: ptr) : slprop =
  exists* (xs: Seq.seq (option t)).
    array_pts_to (maybe_repr t_repr esize) esize ealign a 1.0R xs ** pure (Seq.length xs == n)

ghost fn array_claim_all_uninit (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr)
                                (esize: SZ.t) (ealign: SZ.t) (n: SZ.t) (#b: bytes)
  requires mem_pts_to a 1.0R b
  requires pure (len b == SZ.v esize * SZ.v n)
  requires pure (array_aligned (SZ.v esize) (SZ.v ealign) a)
  ensures  array_pts_to_uninit t_repr (SZ.v esize) (SZ.v ealign) (SZ.v n) a
{
  array_claim_uninit t_repr a esize ealign n;
  fold array_pts_to_uninit t_repr (SZ.v esize) (SZ.v ealign) (SZ.v n) a;
}

ghost fn array_reveal_all_uninit (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr)
                                 (esize: SZ.t) (ealign: SZ.t) (n: SZ.t)
  requires array_pts_to_uninit t_repr (SZ.v esize) (SZ.v ealign) (SZ.v n) a
  ensures  exists* b. mem_pts_to a 1.0R b ** pure (len b == SZ.v esize * SZ.v n)
{
  unfold array_pts_to_uninit t_repr (SZ.v esize) (SZ.v ealign) (SZ.v n) a;
  array_forget t_repr a esize ealign;
}

(* Every element of a live array does hold a value, so a live array is storage
   that happens to be full. The `Some`s are added by hand rather than by a
   lemma with a pattern: `somes` appears nowhere else, and this is the only
   direction anything needs it. *)
let somes (#t: Type0) (xs: Seq.seq t) : Seq.seq (option t) =
  Seq.init (Seq.length xs) (fun i -> Some (Seq.index xs i))

ghost fn array_forget_all (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr)
                          (esize: SZ.t) (ealign: SZ.t) (n: SZ.t) (#xs: Seq.seq t)
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a 1.0R xs
  requires pure (Seq.length xs == SZ.v n)
  ensures  array_pts_to_uninit t_repr (SZ.v esize) (SZ.v ealign) (SZ.v n) a
{
  unfold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a 1.0R xs;
  fold array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) (SZ.v ealign) a 1.0R (somes xs);
  fold array_pts_to_uninit t_repr (SZ.v esize) (SZ.v ealign) (SZ.v n) a;
}

(* The same, without being told how long the array is. Giving storage up is
   the one operation whose length the caller usually does not have to hand:
   the ownership being given up says how long it is, and the `freeable` that
   goes with it says how much storage goes back. This is what a `free` of a
   pointer whose ownership a hand-written helper supplied needs, since there
   is no allocation site nearby to have remembered a length. *)
ghost fn array_forget_full (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr)
                           (esize: SZ.t) (ealign: SZ.t) (#xs: Seq.seq t)
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a 1.0R xs
  ensures  exists* b. mem_pts_to a 1.0R b
                      ** pure (len b == SZ.v esize * Seq.length xs)
{
  unfold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a 1.0R xs;
  fold array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) (SZ.v ealign) a 1.0R (somes xs);
  array_forget t_repr a esize ealign;
}

(* And the other way, once every element has been written. This is what the
   loop that fills an array field ends with. *)
ghost fn array_claim_all (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr)
                         (esize: SZ.t) (ealign: SZ.t) (vs: Seq.seq t)
                         (#xs: (xs: Seq.seq (option t) { Seq.length xs == Seq.length vs }))
  requires array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) (SZ.v ealign) a 1.0R xs
  requires pure (forall (i: nat). i < Seq.length vs ==>
                                 Seq.index xs i == Some (Seq.index vs i))
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a 1.0R vs
{
  unfold array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) (SZ.v ealign) a 1.0R xs;
  fold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a 1.0R vs;
}

(* Every element has been written, but nothing has said *which* values were
   written. That is enough: a sequence all of whose elements are `Some` is a
   sequence of values, and which values it is need never be named. This is the
   step a union's array arm takes when the last of its elements is filled --
   the values were written one statement at a time and no term names them all
   at once. *)
let all_some (#t: Type0) (xs: Seq.seq (option t)) : prop =
  forall (i: nat). i < Seq.length xs ==> Some? (Seq.index xs i)

let unsomes (#t: Type0) (xs: Seq.seq (option t) { all_some xs }) : Seq.seq t =
  Seq.init (Seq.length xs) (fun (i: nat { i < Seq.length xs }) -> Some?.v (Seq.index xs i))

ghost fn array_claim_all_somes (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr)
                               (esize: SZ.t) (ealign: SZ.t) (#xs: Seq.seq (option t))
  requires array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) (SZ.v ealign) a 1.0R xs
  requires pure (all_some xs)
  ensures  exists* (vs: Seq.seq t).
             array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a 1.0R vs **
             pure (Seq.length vs == Seq.length xs)
{
  array_claim_all t_repr a esize ealign (unsomes xs);
}

let somes_length (#t: Type0) (xs: Seq.seq t)
  : Lemma (Seq.length (somes xs) == Seq.length xs)
          [SMTPat (Seq.length (somes xs))] = ()

let somes_index (#t: Type0) (xs: Seq.seq t) (i: nat)
  : Lemma (requires i < Seq.length xs)
          (ensures  Seq.index (somes xs) i == Some (Seq.index xs i))
          [SMTPat (Seq.index (somes xs) i)] = ()

(* ---------------------------------------------------------------------------
   Handing a local array to a callee

   A local array is storage that remembers which elements have been written,
   so it is held in the `option` view; a function that takes `T *` wants every
   element to hold a value, so it asks for the plain one. Passing one to the
   other is these two ghost steps and nothing else -- no bytes move, and the
   array is at the same address throughout.

   `array_somes` carries out the obligation that makes the call legal at all:
   C says reading an uninitialised object is undefined, so a callee that may
   read every element may only be given an array where every element has been
   written. That is exactly its precondition.

   The `xs == somes vs` it leaves behind is what lets the caller put its own
   view back together afterwards: `array_unsomes` returns `somes vs`, and the
   equation says that is the sequence it started with. *)
(* Every cell holding a value, stated over the indices a C loop counts with.
   An invariant over `size_t j` gives Z3 nothing to instantiate for a `nat`;
   the length fitting in a `size_t` is what bridges the two. *)
let all_some_sz (#t: Type0) (xs: Seq.seq (option t)) : prop =
  forall (i: SZ.t). SZ.v i < Seq.length xs ==> Some? (Seq.index xs (SZ.v i))

let all_some_of_sz (#t: Type0) (xs: Seq.seq (option t))
  : Lemma (requires SZ.fits (Seq.length xs) /\ all_some_sz xs)
          (ensures  forall (i: nat). i < Seq.length xs ==> Some? (Seq.index xs i))
  = let aux (i: nat) : Lemma (i < Seq.length xs ==> Some? (Seq.index xs i)) =
      if i < Seq.length xs then begin
        SZ.fits_lte i (Seq.length xs);
        assert (SZ.v (SZ.uint_to_t i) == i)
      end
    in
    Classical.forall_intro aux

let length_fits (esize n m: nat)
  : Lemma (requires esize * n <= m /\ SZ.fits m)
          (ensures  esize > 0 ==> SZ.fits n)
  = if esize > 0 then begin
      M.lemma_mult_le_right n 1 esize;
      SZ.fits_lte n m
    end

(* An array's length fits in a `size_t` when its elements take up room: the
   bytes are owned, and a live range ends at an address that fits. *)
ghost fn array_length_fits (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                           (#p: perm) (#xs: Seq.seq t)
  preserves array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  ensures   pure (SZ.v esize > 0 ==> SZ.fits (Seq.length xs))
{
  unfold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs;
  with b. assert (mem_pts_to a p b ** pure (array_repr t_repr (SZ.v esize) xs b));
  mem_pts_to_fits a;
  length_fits (SZ.v esize) (Seq.length xs) (addr_of a + len b);
  fold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs;
}

ghost fn array_somes (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                     (#p: perm) (#xs: Seq.seq (option t))
  requires array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) (SZ.v ealign) a p xs
  requires pure ((forall (i: nat). i < Seq.length xs ==> Some? (Seq.index xs i)) \/
                 (SZ.v esize > 0 /\ all_some_sz xs))
  ensures  exists* (vs: Seq.seq t).
             array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p vs **
             pure (xs == somes vs /\ Seq.length vs == Seq.length xs /\
                   (forall (i: nat). {:pattern Seq.index vs i}
                     i < Seq.length vs ==> Seq.index xs i == Some (Seq.index vs i)))
{
  array_length_fits (maybe_repr t_repr (SZ.v esize)) a esize ealign;
  Classical.move_requires all_some_of_sz xs;
  unfold array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) (SZ.v ealign) a p xs;
  let vs : Seq.seq t = Seq.init (Seq.length xs) (fun i -> Some?.v (Seq.index xs i));
  Seq.lemma_eq_intro xs (somes vs);
  fold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p vs;
}

ghost fn array_unsomes (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                       (#p: perm) (#vs: Seq.seq t)
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p vs
  ensures  array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) (SZ.v ealign) a p (somes vs)
{
  unfold array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p vs;
  fold array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) (SZ.v ealign) a p (somes vs);
}

(* `s[i] <- s[i]` is `s`.

   A cell borrowed only to read still comes back through `array_unfocus`,
   whose postcondition names the *updated* sequence -- the emitter cannot
   always tell in advance that the borrow will not be written, and
   `array_unfocus_read` is only reachable when it can. The two sequences are
   extensionally equal but not syntactically so, which is the one thing
   slprop matching cannot bridge on its own, so a read-only borrow failed on
   an obligation that has nothing to do with what the C did. One extensional
   step is all it needs, and the pattern is specific enough to cost nothing
   elsewhere. *)
let upd_index_eq (#t: Type) (s: Seq.seq t) (i: nat)
  : Lemma (requires i < Seq.length s)
          (ensures Seq.upd s i (Seq.index s i) == s)
          [SMTPat (Seq.upd s i (Seq.index s i))]
  = Seq.lemma_eq_elim (Seq.upd s i (Seq.index s i)) s

(* A non-empty array's base address is not null, and names a real allocation.

   This is `mem_pts_to_not_null` carried through the definition: the bytes an
   array owns are `esize * length` of them, so a non-empty array of non-empty
   elements owns at least one byte, and owning a byte is what rules out the
   empty provenance. A caller reaches for it when it has to say that an
   interior pointer -- the address of an array field, say -- is not null,
   which no amount of pointer arithmetic can establish on its own. *)
ghost fn array_pts_to_not_null (#t: Type0) (t_repr: t -> bytes -> prop)
                               (esize: nat) (ealign: nat) (a: ptr)
                               (#p: perm) (#xs: Seq.seq t)
  preserves array_pts_to t_repr esize ealign a p xs
  requires  pure (esize > 0 /\ Seq.length xs > 0)
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold array_pts_to t_repr esize ealign a p xs;
  with b. assert mem_pts_to a p b;
  M.lemma_mult_le_right esize 1 (Seq.length xs);
  mem_pts_to_not_null a;
  fold array_pts_to t_repr esize ealign a p xs;
}

(* A pointer walked through an array shares the array's provenance, so when
   the array is a real allocation -- whenever it is non-empty -- no position
   in it is null. This is what lets a function return a walked pointer as a
   found-it result and the caller tell it from `NULL`. *)
ghost fn array_walk_base (#t: Type0) (t_repr: t -> bytes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                         (#p: perm) (#xs: Seq.seq t)
  preserves array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  ensures   pure (SZ.v esize > 0 /\ Seq.length xs > 0 ==> Some? (prov_of a))
{
  if (SZ.v esize > 0 && Seq.length xs > 0) {
    array_pts_to_not_null t_repr (SZ.v esize) (SZ.v ealign) a;
  }
}

let walk_not_null (esize: nat) (a q: ptr)
  : Lemma (requires walk_ok esize a q /\ Some? (prov_of a))
          (ensures  ~(q == null) /\ not (is_null q))
          [SMTPat (walk_ok esize a q)]
  = null_addr

(* ---------------------------------------------------------------------------
   Element refinements

   `seq_forall p xs`: every element of `xs` satisfies `p`. This is how a pure
   `_refine` on a struct declaration reaches the elements of an `_array` of that
   struct: PAL names the refinement `struct_X__refine` in the struct's module
   and states `seq_forall struct_X__refine xs` beside the array's points-to.

   It is opaque to the SMT solver on purpose. A bare
   `forall i. i < length xs ==> p (index xs i)` sits in every query in its
   scope, one copy per refined array, and without an explicit pattern Z3
   chooses its own trigger. Here the quantifier is never seen; the lemmas below
   expose exactly what generated code needs, on patterns that bound
   instantiation:

   - reading a cell: `seq_forall_elim` fires only when the predicate AND a
     concrete read `Seq.index xs i` are both present -- once per read;
   - building a new sequence: one introduction per constructor the array
     operations produce (`upd`, `slice`, `append`, `create`), each firing only
     on the goal `seq_forall p (<constructor> ...)`.

   `seq_forall_reveal` is the manual escape hatch; it has no pattern.
   --------------------------------------------------------------------------- *)

[@@"opaque_to_smt"]
let seq_forall (#t: Type) (p: t -> prop) (xs: Seq.seq t) : prop =
  forall (i: nat). {:pattern (Seq.index xs i)}
    i < Seq.length xs ==> p (Seq.index xs i)

let seq_forall_reveal (#t: Type) (p: t -> prop) (xs: Seq.seq t)
  : Lemma (seq_forall p xs <==>
           (forall (i: nat). i < Seq.length xs ==> p (Seq.index xs i)))
  = reveal_opaque (`%seq_forall) (seq_forall p xs)

let seq_forall_elim (#t: Type) (p: t -> prop) (xs: Seq.seq t) (i: nat)
  : Lemma (requires seq_forall p xs /\ i < Seq.length xs)
          (ensures p (Seq.index xs i))
          [SMTPat (seq_forall p xs); SMTPat (Seq.index xs i)]
  = seq_forall_reveal p xs

let seq_forall_upd (#t: Type) (p: t -> prop) (xs: Seq.seq t) (i: nat) (y: t)
  : Lemma (requires seq_forall p xs /\ i < Seq.length xs /\ p y)
          (ensures seq_forall p (Seq.upd xs i y))
          [SMTPat (seq_forall p (Seq.upd xs i y))]
  = seq_forall_reveal p xs;
    seq_forall_reveal p (Seq.upd xs i y)

let seq_forall_slice (#t: Type) (p: t -> prop) (xs: Seq.seq t) (i j: nat)
  : Lemma (requires seq_forall p xs /\ i <= j /\ j <= Seq.length xs)
          (ensures seq_forall p (Seq.slice xs i j))
          [SMTPat (seq_forall p (Seq.slice xs i j))]
  = seq_forall_reveal p xs;
    seq_forall_reveal p (Seq.slice xs i j)

let seq_forall_append (#t: Type) (p: t -> prop) (xs ys: Seq.seq t)
  : Lemma (requires seq_forall p xs /\ seq_forall p ys)
          (ensures seq_forall p (Seq.append xs ys))
          [SMTPat (seq_forall p (Seq.append xs ys))]
  = seq_forall_reveal p xs;
    seq_forall_reveal p ys;
    seq_forall_reveal p (Seq.append xs ys)

let seq_forall_create (#t: Type) (p: t -> prop) (n: nat) (x: t)
  : Lemma (requires p x)
          (ensures seq_forall p (Seq.create n x))
          [SMTPat (seq_forall p (Seq.create n x))]
  = seq_forall_reveal p (Seq.create n x)

(* An `_out` array of a refined struct leaves the function as a value with the
   element fact: `array_somes`, with the refinement asked of every written cell
   and given back of the sequence it claims. Like `array_somes` it accepts the
   cells indexed by `nat` or, for a loop that counted with a `size_t`, by
   `SZ.t`. *)
let all_some_forall_sz (#t: Type0) (p: t -> prop) (xs: Seq.seq (option t)) : prop =
  forall (i: SZ.t). SZ.v i < Seq.length xs ==>
    Some? (Seq.index xs (SZ.v i)) /\ p (Some?.v (Seq.index xs (SZ.v i)))

let all_some_forall_of_sz (#t: Type0) (p: t -> prop) (xs: Seq.seq (option t))
  : Lemma (requires SZ.fits (Seq.length xs) /\ all_some_forall_sz p xs)
          (ensures  forall (i: nat). i < Seq.length xs ==>
                      Some? (Seq.index xs i) /\ p (Some?.v (Seq.index xs i)))
  = let aux (i: nat)
      : Lemma (i < Seq.length xs ==> Some? (Seq.index xs i) /\ p (Some?.v (Seq.index xs i))) =
      if i < Seq.length xs then begin
        SZ.fits_lte i (Seq.length xs);
        assert (SZ.v (SZ.uint_to_t i) == i)
      end
    in
    Classical.forall_intro aux

let seq_forall_of_somes (#t: Type0) (p: t -> prop) (xs: Seq.seq (option t)) (vs: Seq.seq t)
  : Lemma (requires Seq.length vs == Seq.length xs /\
                    (forall (i: nat). i < Seq.length vs ==> Seq.index xs i == Some (Seq.index vs i)) /\
                    (forall (i: nat). i < Seq.length xs ==>
                       Some? (Seq.index xs i) /\ p (Some?.v (Seq.index xs i))))
          (ensures  seq_forall p vs)
  = let aux (i: nat) : Lemma (i < Seq.length vs ==> p (Seq.index vs i)) =
      if i < Seq.length vs then begin
        assert (Seq.index xs i == Some (Seq.index vs i));
        assert (p (Some?.v (Seq.index xs i)))
      end
    in
    Classical.forall_intro aux;
    seq_forall_reveal p vs

ghost fn array_somes_forall (#t: Type0) (p: t -> prop) (t_repr: t -> bytes -> prop) (a: ptr)
                            (esize: SZ.t) (ealign: SZ.t)
                            (#pm: perm) (#xs: Seq.seq (option t))
  requires array_pts_to (maybe_repr t_repr (SZ.v esize)) (SZ.v esize) (SZ.v ealign) a pm xs
  requires pure ((forall (i: nat). i < Seq.length xs ==>
                    Some? (Seq.index xs i) /\ p (Some?.v (Seq.index xs i))) \/
                 (SZ.v esize > 0 /\ all_some_forall_sz p xs))
  ensures  exists* (vs: Seq.seq t).
             array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a pm vs **
             pure (xs == somes vs /\ Seq.length vs == Seq.length xs /\
                   (forall (i: nat). {:pattern Seq.index vs i}
                     i < Seq.length vs ==> Seq.index xs i == Some (Seq.index vs i)) /\
                   seq_forall p vs)
{
  array_length_fits (maybe_repr t_repr (SZ.v esize)) a esize ealign;
  Classical.move_requires (all_some_forall_of_sz p) xs;
  array_somes t_repr a esize ealign;
  with vs. assert array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a pm vs;
  seq_forall_of_somes p xs vs;
  assert pure (seq_forall p vs);
}
