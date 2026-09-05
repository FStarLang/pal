module Pulse.Lib.C.Palow.ConstSeq

(* ---------------------------------------------------------------------------
   A constant sequence, from a list.

   This is what a `_pure const T a[N] = { ... }` global is published as. The
   obvious encoding -- `Seq.create` with one `Seq.upd` per element -- does not
   scale: checking it against a length refinement costs a subtyping step per
   element, and a thousand-element table then dominates an entire run.

   A flat list fixes both halves of that. The value is one application rather
   than a chain, the length comes out of `normalize_term` in an implicit rather
   than from the solver, and indexing reduces one cons at a time under the
   patterns below.

   `const_seq` is abstract on purpose, and that is the part that actually
   matters. Left transparent it is `Seq.seq_of_list`, which is recursive, and
   the solver unfolds it instead of using the indexing lemma -- which works for
   the first few elements and then stops. Abstract, the lemma is the only route
   in, so the cost is one instantiation per index however long the list is.
   This mirrors `array_spec_of_list` in the existing model, for the same
   reason.
   --------------------------------------------------------------------------- *)

module L = FStar.List.Tot
module Seq = FStar.Seq

val const_seq (#a: Type) (xs: list a) : Seq.seq a

val const_seq_len (#a: Type) (xs: list a)
  : Lemma (Seq.length (const_seq xs) == L.length xs)
          [SMTPat (const_seq xs)]

val const_seq_index (#a: Type) (xs: list a) (i: nat)
  : Lemma (requires i < L.length xs)
          (ensures  Seq.index (const_seq xs) i == L.index xs i)
          [SMTPat (Seq.index (const_seq xs) i)]

(* Walking the list one cons at a time, so that indexing a constant table costs
   the solver a step per index rather than an unfolding of the whole value. *)

let list_length_cons (#a: Type) (x: a) (xs: list a)
  : Lemma (L.length (x :: xs) == L.length xs + 1)
          [SMTPat (L.length (x :: xs))] = ()

let list_index_zero (#a: Type) (x: a) (xs: list a)
  : Lemma (L.index (x :: xs) 0 == x)
          [SMTPat (L.index (x :: xs) 0)] = ()

let list_index_pos (#a: Type) (x: a) (xs: list a) (i: nat)
  : Lemma (requires 0 < i /\ i < L.length xs + 1)
          (ensures  L.index (x :: xs) i == L.index xs (i - 1))
          [SMTPat (L.index (x :: xs) i)] = ()

(* The length is discharged by the normalizer rather than by SMT, which is why
   it is an implicit `squash` and not a refinement on `xs`. *)
let const_seq_with_len (#a: Type) (xs: list a) (n: nat)
                       (#_: normalize_term (L.length xs) == n)
  : (s: Seq.seq a { Seq.length s == n }) =
  const_seq_len xs;
  const_seq xs
