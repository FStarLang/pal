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
open Pulse.Lib.C.Palow.Index

module SZ = FStar.SizeT
module Seq = FStar.Seq
module M = FStar.Math.Lemmas
module ET = Pulse.Lib.C.Palow.Etype

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
   what makes element `i` aligned whenever the base is. Carrying it inside the
   predicate rather than demanding it at each use means a split, a focus and a
   `+! esize` all preserve alignment without anyone restating it. *)
(* Same shape as `aligned`, and opaque for the same reason: the divisibility
   of the address is hidden behind `divides_addr` so that a proof carrying many
   of these facts at once does not hand Z3 a pile of nonlinear arithmetic. *)
let array_aligned (esize: nat) (ealign: nat) (a: ptr) : prop =
  esize > 0 /\ ealign > 0 /\ esize % ealign == 0 /\ divides_addr a ealign

let array_aligned_add (esize: nat) (ealign: nat) (a: ptr) (n: SZ.t)
  : Lemma (requires array_aligned esize ealign a /\ SZ.v n % esize == 0)
          (ensures  array_aligned esize ealign (a +! n))
  = reveal_opaque (`%divides_addr) divides_addr;
    FStar.Math.Lemmas.lemma_div_exact (SZ.v n) esize;
    FStar.Math.Lemmas.lemma_div_exact esize ealign;
    FStar.Math.Lemmas.paren_mul_right (SZ.v n / esize) (esize / ealign) ealign;
    FStar.Math.Lemmas.multiple_modulo_lemma ((SZ.v n / esize) * (esize / ealign)) ealign;
    FStar.Math.Lemmas.modulo_distributivity (addr_of a) (SZ.v n) ealign

(* The form every split actually has: the offset is a whole number of
   elements. *)
let array_aligned_step (esize: nat) (ealign: nat) (a: ptr) (n: SZ.t) (k: nat)
  : Lemma (requires array_aligned esize ealign a /\ SZ.v n == esize * k)
          (ensures  array_aligned esize ealign (a +! n))
  = FStar.Math.Lemmas.swap_mul esize k;
    FStar.Math.Lemmas.multiple_modulo_lemma k esize;
    array_aligned_add esize ealign a n

(* Element `i`'s slice of an index, cut at exactly the offsets `elem_bytes`
   cuts the bytes, and total for the same reason. *)
let elem_etypes (esize: nat) (e: ET.etypes) (i: nat) : ET.etypes =
  let lo = esize * i in
  let hi = lo + esize in
  if hi <= ET.elen e then Seq.slice e lo hi else Seq.empty

let elems_ok (eok: ET.etypes -> prop) (esize: nat) (n: nat) (e: ET.etypes) : prop =
  ET.elen e == esize * n /\ ET.allocated e /\
  (forall (i: nat). i < n ==> eok (elem_etypes esize e i))

let array_pts_to (#t: Type) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (esize: nat) (ealign: nat)
                 ([@@@mkey] a: ptr) (p: perm) (xs: Seq.seq t) : slprop =
  exists* b e. mem_pts_to_at a p b e
             ** pure (array_repr t_repr esize xs b /\ array_aligned esize ealign a
                      /\ elems_ok eok esize (Seq.length xs) e)

(* Giving a read-only share of literal storage back. Literal storage is
   static and nobody owns it, so a share of it is simply dropped; this is
   proved, not assumed.

   Acquiring one is *not* here. It would have to read `t_repr`, `esize` and
   `ealign` as parameters, and a trusted function that produces
   `array_pts_to t_repr eok ...` for a `t_repr` of the caller's choosing is false:
   instantiate it with a relation no byte string satisfies and `array_repr`
   -- which conjoins `t_repr` at every element -- is `False`, so the
   postcondition yields `pure False` from `emp`. A `_ghost_stmt` can say that
   in C. The acquisition is therefore emitted per literal, with the element
   type's own representation written in, next to the function that uses it:
   each such assumption is a statement about one piece of static data, in the
   same way an immutable global's `acquire_var_*` is. *)
ghost fn literal_share_drop (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop)
                            (esize: SZ.t) (ealign: SZ.t) (xs: list t)
  requires exists* p. array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign)
             (literal_addr xs) p (Pulse.Lib.C.Palow.ConstSeq.const_seq xs)
  ensures  emp
{
  drop_ (exists* p. array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign)
           (literal_addr xs) p (Pulse.Lib.C.Palow.ConstSeq.const_seq xs))
}

(* The two directions between an array's ownership and the bytes under it.
   Every scalar type publishes this pair under its own name, and a union arm
   or a structure field has to be able to ask for it without knowing which
   kind of thing it is holding. `array_pts_to` is a definition, so both are
   a fold. *)
ghost fn array_conceal (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                       (#p: perm) (#b: bytes) (#e: ET.etypes) (#xs: Seq.seq t)
  requires mem_pts_to_at a p b e
  requires pure (array_repr t_repr (SZ.v esize) xs b)
  requires pure (array_aligned (SZ.v esize) (SZ.v ealign) a)
  requires pure (elems_ok eok (SZ.v esize) (Seq.length xs) e)
  ensures  array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p xs
{
  fold (array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p xs);
}

ghost fn array_reveal (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                      (#p: perm) (#xs: Seq.seq t)
  requires array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p xs
  ensures  exists* b e. mem_pts_to_at a p b e
             ** pure (array_repr t_repr (SZ.v esize) xs b
                      /\ elems_ok eok (SZ.v esize) (Seq.length xs) e)
{
  unfold (array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p xs);
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
   The effective-type side condition

   An array's index condition is *pointwise*: each element's own byte range is
   acceptable to the element type's own `_etype_ok`, and nothing is asserted
   about the range as a whole. The condition is a predicate rather than a
   `ctype` because a struct states its own condition field by field, and
   field-wise readability does not reassemble into readability at the struct
   type (`access_ok` goes down, not up); carrying the predicate lets the array
   layer and the struct layer share one carrier. The alternative -- carrying readability at `TArr` over the
   whole extent -- does not survive a join. `read_ok` splits
   (`Etype.read_ok_slice`) but does not recombine: `Etype.fst:743` proves the
   converse fails, so `array_join` could not re-establish its own
   postcondition, and retyping at the join is not available either because
   `mem_store_etypes` demands `p == 1.0R` while a join happens at an arbitrary
   permission.

   The pointwise form, being literally the conjunction of the parts, splits and
   joins by construction. The price is that an `int32_t[10]` and ten adjacent
   standalone `int32_t`s stay interchangeable; puns that differ at a scalar
   leaf -- int vs. float, int vs. pointer -- are still caught, and those are
   the ones 6.5p7 is about.
   --------------------------------------------------------------------------- *)

(* The two `elem_bytes_*` lemmas again, for indices. They are restated rather
   than shared because `elem_bytes` is fixed at `bytes` and is named in enough
   places -- including generated code -- that generalising it is not worth the
   churn. *)
let elem_etypes_prefix (esize: nat) (e: ET.etypes) (n: nat) (i: nat)
  : Lemma (requires esize * n <= ET.elen e /\ i < n)
          (ensures  elem_etypes esize (Seq.slice e 0 (esize * n)) i
                    == elem_etypes esize e i)
  = elem_fits esize n i;
    Seq.slice_slice e 0 (esize * n) (esize * i) (esize * i + esize)

let elem_etypes_suffix (esize: nat) (e: ET.etypes) (n: nat) (i: nat)
  : Lemma (requires esize * n <= ET.elen e /\ esize * (n + i) + esize <= ET.elen e)
          (ensures  elem_etypes esize (Seq.slice e (esize * n) (ET.elen e)) i
                    == elem_etypes esize e (n + i))
  = M.distributivity_add_right esize n i;
    Seq.slice_slice e (esize * n) (ET.elen e) (esize * i) (esize * i + esize)

(* `append_slice_left`/`append_slice_right` from `Bytes`, for indices. *)
let etypes_append_left (e1 e2: ET.etypes)
  : Lemma (Seq.slice (Seq.append e1 e2) 0 (ET.elen e1) == e1)
  = Seq.lemma_eq_intro (Seq.slice (Seq.append e1 e2) 0 (ET.elen e1)) e1

let etypes_append_right (e1 e2: ET.etypes)
  : Lemma (Seq.slice (Seq.append e1 e2) (ET.elen e1) (ET.elen e1 + ET.elen e2) == e2)
  = Seq.lemma_eq_intro
      (Seq.slice (Seq.append e1 e2) (ET.elen e1) (ET.elen e1 + ET.elen e2)) e2

let etypes_slice_append_left (e1 e2: ET.etypes) (i: nat) (j: nat { i <= j /\ j <= ET.elen e1 })
  : Lemma (Seq.slice (Seq.append e1 e2) i j == Seq.slice e1 i j)
  = etypes_append_left e1 e2;
    Seq.slice_slice (Seq.append e1 e2) 0 (ET.elen e1) i j

#push-options "--z3rlimit 40"
let elems_ok_split (eok: ET.etypes -> prop) (esize: nat) (m: nat) (e: ET.etypes) (n: nat)
  : Lemma (requires elems_ok eok esize m e /\ n <= m)
          (ensures  esize * n <= ET.elen e /\
                    elems_ok eok esize n (Seq.slice e 0 (esize * n)) /\
                    elems_ok eok esize (m - n) (Seq.slice e (esize * n) (ET.elen e)))
  = M.lemma_mult_le_right esize n m;
    let pre = Seq.slice e 0 (esize * n) in
    let post = Seq.slice e (esize * n) (ET.elen e) in
    let aux_pre (i: nat) : Lemma (i < n ==> eok (elem_etypes esize pre i)) =
      if i < n then elem_etypes_prefix esize e n i
    in
    Classical.forall_intro aux_pre;
    let aux_post (i: nat)
      : Lemma (i < m - n ==> eok (elem_etypes esize post i)) =
      if i < m - n then begin
        elem_fits esize m (n + i);
        elem_etypes_suffix esize e n i
      end
    in
    Classical.forall_intro aux_post;
    M.distributivity_sub_right esize m n
#pop-options

(* The join is where the nonlinear arithmetic actually bites: the suffix's
   element `j` is the whole array's element `n + j`, and relating the two
   offsets needs `esize * (i - n) == esize * i - esize * n`, which Z3 will not
   find on its own at any rlimit. Supplying the two distributivity instances
   explicitly is what makes this go through. *)
#push-options "--z3rlimit 40"
let elems_ok_join (eok: ET.etypes -> prop) (esize: nat) (e1 e2: ET.etypes) (n m: nat)
  : Lemma (requires elems_ok eok esize n e1 /\ elems_ok eok esize m e2)
          (ensures  elems_ok eok esize (n + m) (Seq.append e1 e2))
  = let e = Seq.append e1 e2 in
    M.distributivity_add_right esize n m;
    let aux (i: nat) : Lemma (i < n + m ==> eok (elem_etypes esize e i)) =
      if i < n then begin
        elem_fits esize n i;
        Seq.slice_slice e 0 (ET.elen e1) (esize * i) (esize * i + esize);
        etypes_append_left e1 e2
      end else if i < n + m then begin
        let j = i - n in
        elem_fits esize m j;
        M.distributivity_sub_left esize i n;
        M.distributivity_add_right esize n j;
        etypes_append_right e1 e2;
        Seq.slice_slice e (ET.elen e1) (ET.elen e) (esize * j) (esize * j + esize)
      end
    in
    Classical.forall_intro aux
#pop-options

(* A one-element array's condition is its element's condition: `elem_etypes`
   at 0 is the whole range. This is the index half of `singleton_repr`. *)
let elems_ok_one (eok: ET.etypes -> prop) (esize: nat) (e: ET.etypes)
  : Lemma (requires ET.elen e == esize)
          (ensures  (elems_ok eok esize 1 e <==> (eok e /\ ET.allocated e)))
  = assert (elem_etypes esize e 0 == Seq.slice e 0 esize);
    Seq.lemma_eq_intro (Seq.slice e 0 esize) e

(* Freshly allocated storage satisfies the condition at *any* element type
   whose size matches the stride: every byte is `None`, and no element
   condition asks anything of a `None` byte. This is what makes "malloc, then
   use it as a T[n]" legal without a retyping step, and it is the only reason
   the index does not need a `fixed` flag threaded through the array layer.
   The caller supplies the element type's own half of that, which every
   generated `{t}_etype_ok_none` discharges. *)
let elems_ok_none (eok: ET.etypes -> prop) (esize: nat) (n: nat)
  : Lemma (requires eok (ET.etypes_none esize))
          (ensures  elems_ok eok esize n (ET.etypes_none (esize * n)))
  = let e = ET.etypes_none (esize * n) in
    let aux (i: nat) : Lemma (i < n ==> eok (elem_etypes esize e i)) =
      if i < n then begin
        elem_fits esize n i;
        Seq.lemma_eq_elim (elem_etypes esize e i) (ET.etypes_none esize)
      end
    in
    Classical.forall_intro aux

(* An array that is readable as a whole is readable element by element. This
   is how a store at the array type -- which is what a union member switch
   does -- lands back in the pointwise form the array layer carries. *)
let elems_ok_read_ok (eok: ET.etypes -> prop) (ect: ET.ctype) (esize: nat) (n: nat) (e: ET.etypes)
  : Lemma (requires (forall (e': ET.etypes). ET.read_ok e' ect /\ ET.allocated e'
                                             /\ ET.elen e' == esize ==> eok e')
                    /\ ET.csize ect == esize /\ ET.elen e == esize * n
                    /\ ET.allocated e /\ ET.read_ok e (ET.TArr ect n))
          (ensures  elems_ok eok esize n e)
  = let aux (i: nat) : Lemma (i < n ==> eok (elem_etypes esize e i)) =
      if i < n then begin
        elem_fits esize n i;
        if esize = 0 then ()
        else begin
          M.multiple_modulo_lemma i esize;
          assert (ET.emod (esize * i) esize == 0);
          assert (ET.access_ok ect 0 ect);
          assert (ET.access_ok (ET.TArr ect n) (esize * i) ect);
          ET.read_ok_sub e (ET.TArr ect n) (esize * i) ect
        end
      end
    in
    Classical.forall_intro aux

(* Storage that carries no effective type at all is claimable as an array of
   any element type that fits it: `read_ok` holds at every type on an entry
   with no effective type yet. This is the bridge from a union's storage --
   which a union's `_pts_to` keeps untyped, since 6.5.2.3p3 lets any member be
   read -- to an array member of that union. *)
let elems_ok_untyped (eok: ET.etypes -> prop) (esize: nat) (n: nat) (e: ET.etypes)
  : Lemma (requires (forall (e': ET.etypes). ET.untyped e' /\ ET.elen e' == esize ==> eok e')
                    /\ ET.untyped e /\ ET.elen e == esize * n)
          (ensures  elems_ok eok esize n e)
  = let aux (i: nat) : Lemma (i < n ==> eok (elem_etypes esize e i)) =
      if i < n then begin
        elem_fits esize n i;
        ET.untyped_slice e (esize * i) (esize * i + esize)
      end
    in
    Classical.forall_intro aux

(* The quantified form, for generated code that cannot name the index it is
   about to claim at: after a chain of splits the slice is several `Seq.slice`
   deep and only the solver knows which one it is. *)
let elems_ok_untyped_all (eok: ET.etypes -> prop) (esize: nat) (n: nat)
  : Lemma (requires (forall (e': ET.etypes). ET.untyped e' /\ ET.elen e' == esize ==> eok e'))
          (ensures  (forall (e: ET.etypes). ET.untyped e /\ ET.elen e == esize * n
                                       ==> elems_ok eok esize n e))
  = Classical.forall_intro (Classical.move_requires (elems_ok_untyped eok esize n))


(* ---------------------------------------------------------------------------
   Ownership split and join

   `off` is passed in rather than computed as `esize * n` so that the caller
   supplies the `size_t` multiplication (and its overflow proof) at the point
   where it is known to fit; PAL always knows the offset statically.
   --------------------------------------------------------------------------- *)

ghost fn array_split (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                     (#p: perm) (#xs: Seq.seq t)
                     (n: SZ.t { SZ.v n <= Seq.length xs })
                     (off: SZ.t { SZ.v off == SZ.v esize * SZ.v n })
  requires array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p xs
  ensures  array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p (Seq.slice xs 0 (SZ.v n))
  ensures  array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) (a +! off) p
                        (Seq.slice xs (SZ.v n) (Seq.length xs))
  ensures  pure (array_aligned (SZ.v esize) (SZ.v ealign) (a +! off))
{
  unfold array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p xs;
  with b e. assert (mem_pts_to_at a p b e ** pure (array_repr t_repr (SZ.v esize) xs b));
  array_repr_split t_repr (SZ.v esize) xs b (SZ.v n);
  elems_ok_split eok (SZ.v esize) (Seq.length xs) e (SZ.v n);
  array_aligned_step (SZ.v esize) (SZ.v ealign) a off (SZ.v n);
  mem_split_at a off;
  fold array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p (Seq.slice xs 0 (SZ.v n));
  fold array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) (a +! off) p
                    (Seq.slice xs (SZ.v n) (Seq.length xs));
}

ghost fn array_join (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                    (off: SZ.t) (#p: perm) (#xs #ys: Seq.seq t)
  requires array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p xs
  requires array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) (a +! off) p ys
  requires pure (SZ.v off == SZ.v esize * Seq.length xs)
  ensures  array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p (Seq.append xs ys)
{
  unfold array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p xs;
  with b1 e1. assert (mem_pts_to_at a p b1 e1
                      ** pure (array_repr t_repr (SZ.v esize) xs b1));
  unfold array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) (a +! off) p ys;
  with b2 e2. assert (mem_pts_to_at (a +! off) p b2 e2
                      ** pure (array_repr t_repr (SZ.v esize) ys b2));
  mem_join_at a #p #b1 #b2 #e1 #e2 off;
  array_repr_join t_repr (SZ.v esize) xs ys b1 b2;
  elems_ok_join eok (SZ.v esize) e1 e2 (Seq.length xs) (Seq.length ys);
  fold array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p (Seq.append xs ys);
}

(* ---------------------------------------------------------------------------
   Individual elements

   `elem_pts_to` is the generic shape of a layer-1 points-to: the concrete
   scalar predicates in `Pulse.Lib.C.Palow.Scalar` are definitionally equal to
   it (their representation happens to be unique, so they drop the
   existential), and a generated struct predicate is literally this.
   --------------------------------------------------------------------------- *)

let elem_pts_to (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop)
                ([@@@mkey] a: ptr) (p: perm) (x: t) : slprop =
  exists* b e. mem_pts_to_at a p b e
               ** pure (t_repr x b /\ ET.elen e == len b /\ ET.allocated e /\ eok e)

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

ghost fn array_singleton_elim (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                              (#p: perm) (#x: t)
  requires array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p (Seq.create 1 x)
  ensures  elem_pts_to t_repr eok a p x
{
  unfold array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p (Seq.create 1 x);
  with b e. assert (mem_pts_to_at a p b e
                    ** pure (array_repr t_repr (SZ.v esize) (Seq.create 1 x) b));
  singleton_repr_elim t_repr (SZ.v esize) x b;
  elems_ok_one eok (SZ.v esize) e;
  fold elem_pts_to t_repr eok a p x;
}

ghost fn array_singleton_intro (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                               (#p: perm) (#x: t)
  requires elem_pts_to t_repr eok a p x
  requires pure (forall (b: bytes). t_repr x b ==> len b == SZ.v esize)
  requires pure (array_aligned (SZ.v esize) (SZ.v ealign) a)
  ensures  array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p (Seq.create 1 x)
{
  unfold elem_pts_to t_repr eok a p x;
  with b e. assert (mem_pts_to_at a p b e ** pure (t_repr x b));
  singleton_repr t_repr (SZ.v esize) x b;
  elems_ok_one eok (SZ.v esize) e;
  fold array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p (Seq.create 1 x);
}

(* ---------------------------------------------------------------------------
   Focusing on one element

   This is what `a[i]` needs, and it is two `array_split`s: the element lives at
   `a + esize * i`, exactly as C says. Nothing here is array-specific beyond the
   arithmetic -- the ownership transfer is `mem_split`.
   --------------------------------------------------------------------------- *)

ghost fn array_focus (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                     (#p: perm) (#xs: Seq.seq t)
                     (i: SZ.t { SZ.v i < Seq.length xs })
                     (off: SZ.t { SZ.v off == SZ.v esize * SZ.v i })
  requires array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p xs
  ensures  array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p (Seq.slice xs 0 (SZ.v i))
  ensures  elem_pts_to t_repr eok (a +! off) p (Seq.index xs (SZ.v i))
  ensures  array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) ((a +! off) +! esize) p
                        (Seq.slice xs (SZ.v i + 1) (Seq.length xs))
  ensures  pure (array_aligned (SZ.v esize) (SZ.v ealign) (a +! off))
{
  array_split t_repr eok a esize ealign i off;
  let tail = Seq.slice xs (SZ.v i) (Seq.length xs);
  array_split t_repr eok (a +! off) esize ealign #p #tail 1sz esize;
  Seq.lemma_eq_intro (Seq.slice tail 0 1) (Seq.create 1 (Seq.index xs (SZ.v i)));
  rewrite (array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) (a +! off) p (Seq.slice tail 0 1))
       as (array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) (a +! off) p
                        (Seq.create 1 (Seq.index xs (SZ.v i))));
  array_singleton_elim t_repr eok (a +! off) esize ealign;
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

ghost fn array_unfocus (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                       (#p: perm) (#xs: Seq.seq t) (#y: t)
                       (i: SZ.t { SZ.v i < Seq.length xs })
                       (off: SZ.t { SZ.v off == SZ.v esize * SZ.v i })
  requires array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p (Seq.slice xs 0 (SZ.v i))
  requires elem_pts_to t_repr eok (a +! off) p y
  requires array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) ((a +! off) +! esize) p
                        (Seq.slice xs (SZ.v i + 1) (Seq.length xs))
  requires pure (forall (b: bytes). t_repr y b ==> len b == SZ.v esize)
  requires pure (array_aligned (SZ.v esize) (SZ.v ealign) (a +! off))
  ensures  array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p (Seq.upd xs (SZ.v i) y)
{
  array_singleton_intro t_repr eok (a +! off) esize ealign;
  array_join t_repr eok (a +! off) esize ealign esize
             #p #(Seq.create 1 y) #(Seq.slice xs (SZ.v i + 1) (Seq.length xs));
  array_join t_repr eok a esize ealign off
             #p #(Seq.slice xs 0 (SZ.v i))
             #(Seq.append (Seq.create 1 y) (Seq.slice xs (SZ.v i + 1) (Seq.length xs)));
  upd_split xs (SZ.v i) y;
  rewrite (array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p
                        (Seq.append (Seq.slice xs 0 (SZ.v i))
                                    (Seq.append (Seq.create 1 y)
                                                (Seq.slice xs (SZ.v i + 1) (Seq.length xs)))))
       as (array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p (Seq.upd xs (SZ.v i) y));
}

(* The generic layer-1 view of one element, opened and closed. A scalar's own
   `t_reveal`/`t_conceal` produce and consume exactly this shape, so these two
   are the adapters between an array element and the machine operations. *)

ghost fn elem_reveal (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr) (#p: perm) (#x: t)
  requires elem_pts_to t_repr eok a p x
  ensures  exists* b e. mem_pts_to_at a p b e
             ** pure (t_repr x b /\ ET.elen e == len b /\ ET.allocated e /\ eok e)
{
  unfold elem_pts_to t_repr eok a p x;
}

ghost fn elem_conceal (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr)
                      (#p: perm) (#b: bytes) (#e: ET.etypes) (#x: t)
  requires mem_pts_to_at a p b e
  requires pure (t_repr x b /\ ET.elen e == len b /\ ET.allocated e /\ eok e)
  ensures  elem_pts_to t_repr eok a p x
{
  fold elem_pts_to t_repr eok a p x;
}

(* Closing a focus that only read: the sequence that comes back is the one that
   went in. This is `array_unfocus` plus the observation that `Seq.upd xs i
   (Seq.index xs i)` is `xs`, done once here so that every emitted subscript
   read does not have to repeat it. *)
ghost fn array_unfocus_read (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                            (#p: perm) (#xs: Seq.seq t)
                            (i: SZ.t { SZ.v i < Seq.length xs })
                            (off: SZ.t { SZ.v off == SZ.v esize * SZ.v i })
  requires array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p (Seq.slice xs 0 (SZ.v i))
  requires elem_pts_to t_repr eok (a +! off) p (Seq.index xs (SZ.v i))
  requires array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) ((a +! off) +! esize) p
                        (Seq.slice xs (SZ.v i + 1) (Seq.length xs))
  requires pure (forall (b: bytes).
                   t_repr (Seq.index xs (SZ.v i)) b ==> len b == SZ.v esize)
  requires pure (array_aligned (SZ.v esize) (SZ.v ealign) (a +! off))
  ensures  array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p xs
{
  array_unfocus t_repr eok a esize ealign i off;
  Seq.lemma_eq_intro (Seq.upd xs (SZ.v i) (Seq.index xs (SZ.v i))) xs;
  rewrite (array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p (Seq.upd xs (SZ.v i) (Seq.index xs (SZ.v i))))
       as (array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p xs);
}

(* The byte offset of an in-bounds element fits in a `size_t`, so the
   multiplication a subscript needs is well-defined. This is not an extra
   assumption: owning the array means owning `esize * length xs` bytes at `a`,
   and `mem_pts_to_fits` says a live range ends at an address that fits. C says
   the same thing, and for the same reason. *)
ghost fn array_offset_fits (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                           (#p: perm) (#xs: Seq.seq t)
                           (i: SZ.t { SZ.v i < Seq.length xs })
  preserves array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p xs
  ensures   pure (SZ.fits (SZ.v esize * SZ.v i))
{
  unfold array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p xs;
  with b e. assert (mem_pts_to_at a p b e ** pure (array_repr t_repr (SZ.v esize) xs b));
  mem_pts_to_at_fits a;
  elem_fits (SZ.v esize) (Seq.length xs) (SZ.v i);
  SZ.fits_lte (SZ.v esize * SZ.v i) (addr_of a + len b);
  fold array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p xs;
}

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
ghost fn array_claim_uninit (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr)
                            (esize: SZ.t) (ealign: SZ.t) (n: SZ.t)
                            (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v esize * SZ.v n)
  requires pure (array_aligned (SZ.v esize) (SZ.v ealign) a)
  requires pure (elems_ok eok (SZ.v esize) (SZ.v n) e)
  ensures  array_pts_to (maybe_repr t_repr (SZ.v esize)) eok (SZ.v esize) (SZ.v ealign) a 1.0R
                        (Seq.create (SZ.v n) (None #t))
{
  create_repr t_repr (SZ.v esize) (SZ.v n) b;
  fold array_pts_to (maybe_repr t_repr (SZ.v esize)) eok (SZ.v esize) (SZ.v ealign) a 1.0R
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
ghost fn array_claim_zeroed (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr)
                            (esize: SZ.t) (ealign: SZ.t) (n: SZ.t) (#z: t)
                            (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (b == zeroed (SZ.v esize * SZ.v n))
  requires pure (t_repr z (zeroed (SZ.v esize)))
  requires pure (array_aligned (SZ.v esize) (SZ.v ealign) a)
  requires pure (elems_ok eok (SZ.v esize) (SZ.v n) e)
  ensures  array_pts_to (maybe_repr t_repr (SZ.v esize)) eok (SZ.v esize) (SZ.v ealign) a 1.0R
                        (Seq.create (SZ.v n) (Some z))
{
  Classical.forall_intro (Classical.move_requires (elem_bytes_zeroed (SZ.v esize) (SZ.v n)));
  fold array_pts_to (maybe_repr t_repr (SZ.v esize)) eok (SZ.v esize) (SZ.v ealign) a 1.0R
                    (Seq.create (SZ.v n) (Some z));
}

(* And back, at whatever the elements have become. Giving the storage up does
   not depend on what was last written to it, which is why this asks for no
   `Some`. *)
ghost fn array_forget (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                      (#xs: Seq.seq (option t))
  requires array_pts_to (maybe_repr t_repr (SZ.v esize)) eok (SZ.v esize) (SZ.v ealign) a 1.0R xs
  ensures  exists* b. mem_pts_to a 1.0R b
                      ** pure (len b == SZ.v esize * Seq.length xs)
{
  unfold array_pts_to (maybe_repr t_repr (SZ.v esize)) eok (SZ.v esize) (SZ.v ealign) a 1.0R xs;
  mem_hide_etypes a;
}

(* An element that does hold a value, as an ordinary element of `t`. The
   `Some?` is stated as a side condition rather than matched on the implicit,
   because at the point of use what is in context is `Seq.index xs i` and only
   the solver knows it is a `Some`. *)
ghost fn elem_maybe_get (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (esize: SZ.t) (a: ptr)
                        (#p: perm) (#x: (x: option t { Some? x }))
  requires elem_pts_to (maybe_repr t_repr (SZ.v esize)) eok a p x
  ensures  elem_pts_to t_repr eok a p (Some?.v x)
{
  unfold elem_pts_to (maybe_repr t_repr (SZ.v esize)) eok a p x;
  fold elem_pts_to t_repr eok a p (Some?.v x);
}

ghost fn elem_maybe_put (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (esize: SZ.t) (a: ptr)
                        (#p: perm) (#x: t)
  requires elem_pts_to t_repr eok a p x
  ensures  elem_pts_to (maybe_repr t_repr (SZ.v esize)) eok a p (Some x)
{
  unfold elem_pts_to t_repr eok a p x;
  fold elem_pts_to (maybe_repr t_repr (SZ.v esize)) eok a p (Some x);
}

(* The write-only view of one element, whatever it held before. A write to
   `a[i]` goes down to this and comes back up through the type's own
   `t_write_uninit`, which is the same path a scalar local takes. *)
ghost fn elem_maybe_reveal (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (esize: SZ.t) (a: ptr)
                           (#x: option t)
  requires elem_pts_to (maybe_repr t_repr (SZ.v esize)) eok a 1.0R x
  requires pure (forall (v: t) (b: bytes). t_repr v b ==> len b == SZ.v esize)
  ensures  exists* b e. mem_pts_to_at a 1.0R b e
             ** pure (len b == SZ.v esize /\ ET.elen e == len b /\ eok e)
{
  unfold elem_pts_to (maybe_repr t_repr (SZ.v esize)) eok a 1.0R x;
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
let array_pts_to_uninit (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop)
                        (esize: nat) (ealign: nat) (n: nat) ([@@@mkey] a: ptr) : slprop =
  exists* (xs: Seq.seq (option t)).
    array_pts_to (maybe_repr t_repr esize) eok esize ealign a 1.0R xs ** pure (Seq.length xs == n)

ghost fn array_claim_all_uninit (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr)
                                (esize: SZ.t) (ealign: SZ.t) (n: SZ.t)
                                (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v esize * SZ.v n)
  requires pure (array_aligned (SZ.v esize) (SZ.v ealign) a)
  requires pure (elems_ok eok (SZ.v esize) (SZ.v n) e)
  ensures  array_pts_to_uninit t_repr eok (SZ.v esize) (SZ.v ealign) (SZ.v n) a
{
  array_claim_uninit t_repr eok a esize ealign n;
  fold array_pts_to_uninit t_repr eok (SZ.v esize) (SZ.v ealign) (SZ.v n) a;
}

ghost fn array_reveal_all_uninit (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr)
                                 (esize: SZ.t) (ealign: SZ.t) (n: SZ.t)
  requires array_pts_to_uninit t_repr eok (SZ.v esize) (SZ.v ealign) (SZ.v n) a
  ensures  exists* b. mem_pts_to a 1.0R b ** pure (len b == SZ.v esize * SZ.v n)
{
  unfold array_pts_to_uninit t_repr eok (SZ.v esize) (SZ.v ealign) (SZ.v n) a;
  array_forget t_repr eok a esize ealign;
}

(* Every element of a live array does hold a value, so a live array is storage
   that happens to be full. The `Some`s are added by hand rather than by a
   lemma with a pattern: `somes` appears nowhere else, and this is the only
   direction anything needs it. *)
let somes (#t: Type0) (xs: Seq.seq t) : Seq.seq (option t) =
  Seq.init (Seq.length xs) (fun i -> Some (Seq.index xs i))

ghost fn array_forget_all (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr)
                          (esize: SZ.t) (ealign: SZ.t) (n: SZ.t) (#xs: Seq.seq t)
  requires array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a 1.0R xs
  requires pure (Seq.length xs == SZ.v n)
  ensures  array_pts_to_uninit t_repr eok (SZ.v esize) (SZ.v ealign) (SZ.v n) a
{
  unfold array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a 1.0R xs;
  fold array_pts_to (maybe_repr t_repr (SZ.v esize)) eok (SZ.v esize) (SZ.v ealign) a 1.0R (somes xs);
  fold array_pts_to_uninit t_repr eok (SZ.v esize) (SZ.v ealign) (SZ.v n) a;
}

(* The same, without being told how long the array is. Giving storage up is
   the one operation whose length the caller usually does not have to hand:
   the ownership being given up says how long it is, and the `freeable` that
   goes with it says how much storage goes back. This is what a `free` of a
   pointer whose ownership a hand-written helper supplied needs, since there
   is no allocation site nearby to have remembered a length. *)
ghost fn array_forget_full (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr)
                           (esize: SZ.t) (ealign: SZ.t) (#xs: Seq.seq t)
  requires array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a 1.0R xs
  ensures  exists* b. mem_pts_to a 1.0R b
                      ** pure (len b == SZ.v esize * Seq.length xs)
{
  unfold array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a 1.0R xs;
  fold array_pts_to (maybe_repr t_repr (SZ.v esize)) eok (SZ.v esize) (SZ.v ealign) a 1.0R (somes xs);
  array_forget t_repr eok a esize ealign;
}

(* And the other way, once every element has been written. This is what the
   loop that fills an array field ends with. *)
ghost fn array_claim_all (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr)
                         (esize: SZ.t) (ealign: SZ.t) (vs: Seq.seq t)
                         (#xs: (xs: Seq.seq (option t) { Seq.length xs == Seq.length vs }))
  requires array_pts_to (maybe_repr t_repr (SZ.v esize)) eok (SZ.v esize) (SZ.v ealign) a 1.0R xs
  requires pure (forall (i: nat). i < Seq.length vs ==>
                                 Seq.index xs i == Some (Seq.index vs i))
  ensures  array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a 1.0R vs
{
  unfold array_pts_to (maybe_repr t_repr (SZ.v esize)) eok (SZ.v esize) (SZ.v ealign) a 1.0R xs;
  fold array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a 1.0R vs;
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

ghost fn array_claim_all_somes (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr)
                               (esize: SZ.t) (ealign: SZ.t) (#xs: Seq.seq (option t))
  requires array_pts_to (maybe_repr t_repr (SZ.v esize)) eok (SZ.v esize) (SZ.v ealign) a 1.0R xs
  requires pure (all_some xs)
  ensures  exists* (vs: Seq.seq t).
             array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a 1.0R vs **
             pure (Seq.length vs == Seq.length xs)
{
  array_claim_all t_repr eok a esize ealign (unsomes xs);
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
ghost fn array_length_fits (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr)
                           (esize: SZ.t) (ealign: SZ.t) (#p: perm) (#xs: Seq.seq t)
  preserves array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p xs
  ensures   pure (SZ.v esize > 0 ==> SZ.fits (Seq.length xs))
{
  unfold array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p xs;
  with b e. assert (mem_pts_to_at a p b e
                    ** pure (array_repr t_repr (SZ.v esize) xs b));
  mem_pts_to_at_fits a;
  length_fits (SZ.v esize) (Seq.length xs) (addr_of a + len b);
  fold array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p xs;
}

ghost fn array_somes (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                     (#p: perm) (#xs: Seq.seq (option t))
  requires array_pts_to (maybe_repr t_repr (SZ.v esize)) eok (SZ.v esize) (SZ.v ealign) a p xs
  requires pure ((forall (i: nat). i < Seq.length xs ==> Some? (Seq.index xs i)) \/
                 (SZ.v esize > 0 /\ all_some_sz xs))
  ensures  exists* (vs: Seq.seq t).
             array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p vs **
             pure (xs == somes vs /\ Seq.length vs == Seq.length xs /\
                   (forall (i: nat). {:pattern Seq.index vs i}
                     i < Seq.length vs ==> Seq.index xs i == Some (Seq.index vs i)))
{
  array_length_fits (maybe_repr t_repr (SZ.v esize)) eok a esize ealign;
  Classical.move_requires all_some_of_sz xs;
  unfold array_pts_to (maybe_repr t_repr (SZ.v esize)) eok (SZ.v esize) (SZ.v ealign) a p xs;
  let vs : Seq.seq t = Seq.init (Seq.length xs) (fun i -> Some?.v (Seq.index xs i));
  Seq.lemma_eq_intro xs (somes vs);
  fold array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p vs;
}

ghost fn array_unsomes (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop) (a: ptr) (esize: SZ.t) (ealign: SZ.t)
                       (#p: perm) (#vs: Seq.seq t)
  requires array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p vs
  ensures  array_pts_to (maybe_repr t_repr (SZ.v esize)) eok (SZ.v esize) (SZ.v ealign) a p (somes vs)
{
  unfold array_pts_to t_repr eok (SZ.v esize) (SZ.v ealign) a p vs;
  fold array_pts_to (maybe_repr t_repr (SZ.v esize)) eok (SZ.v esize) (SZ.v ealign) a p (somes vs);
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
ghost fn array_pts_to_not_null (#t: Type0) (t_repr: t -> bytes -> prop) (eok: ET.etypes -> prop)
                               (esize: nat) (ealign: nat) (a: ptr)
                               (#p: perm) (#xs: Seq.seq t)
  preserves array_pts_to t_repr eok esize ealign a p xs
  requires  pure (esize > 0 /\ Seq.length xs > 0)
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold array_pts_to t_repr eok esize ealign a p xs;
  with b e. assert (mem_pts_to_at a p b e);
  M.lemma_mult_le_right esize 1 (Seq.length xs);
  mem_pts_to_at_not_null a;
  fold array_pts_to t_repr eok esize ealign a p xs;
}
