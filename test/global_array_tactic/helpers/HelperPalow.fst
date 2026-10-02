module HelperPalow

(* The same fact as `Helper`, for the Palow memory model: there a `_pure` array
   global is published as a `const_seq`, not as an `array_spec`, so the proof
   has to reach the elements through `ConstSeq`'s indexing lemma rather than
   through `array_spec_to_list`.

   The shape of the argument is unchanged, and that is the point: decide
   sortedness on the *list*, where it is a structural recursion the normalizer
   can run, and then carry it across to the sequence in one step. Nothing here
   quantifies over a thousand-element sequence in the solver. *)

open Pulse.Lib.C.Palow.ConstSeq
module L = FStar.List.Tot
module Seq = FStar.Seq
module I32 = FStar.Int32

let is_sorted (xs: list I32.t) =
  forall (i j: nat). i < j /\ j < L.length xs ==>
    I32.v (L.index xs i) <= I32.v (L.index xs j)

let rec compute_sorted (xs: list I32.t) : b:bool { b ==> is_sorted xs } =
  match xs with
  | x::y::xs -> I32.v x <= I32.v y && compute_sorted (y::xs)
  | _ -> true

let is_sorted_of_compute_sorted #xs (h: compute_sorted xs) : is_sorted xs = ()

let is_sorted_seq (s: Seq.seq I32.t) =
  forall (i j: nat). i < j /\ j < Seq.length s ==>
    I32.v (Seq.index s i) <= I32.v (Seq.index s j)

(* `const_seq_len` and `const_seq_index` are both SMT patterns, so this is the
   whole of the bridge: every index of the sequence is the same index of the
   list, and the two lengths agree. *)
let is_sorted_seq_of_list (xs: list I32.t) (h: is_sorted xs)
  : is_sorted_seq (const_seq xs) = ()

open FStar.Tactics.V2

let prove_by_norm () : Tac unit =
  norm [delta_only [`%Global_my_array.var_my_array; `%const_seq_with_len]];
  apply (`is_sorted_seq_of_list);
  apply (`is_sorted_of_compute_sorted);
  compute ()

#set-options "--no_smt"
let my_array_sorted () : is_sorted_seq Global_my_array.var_my_array =
  _ by (prove_by_norm ())
