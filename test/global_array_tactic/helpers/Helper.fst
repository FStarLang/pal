module Helper
open Pulse.Lib.C.Array

let is_sorted (xs: list Int32.t) =
  forall (i j: nat). i < j /\ j < List.length xs ==>
    Int32.v (List.Tot.index xs i) < Int32.v (List.Tot.index xs j)

assume val array_spec_to_list #a (s: full_array_spec a) : list a
assume val array_spec_to_list_len #a s : Lemma (List.length (array_spec_to_list #a s) == array_spec_len s) [SMTPat (List.length (array_spec_to_list #a s))]
assume val array_spec_to_list_idx #a (s: full_array_spec a) (i: nat) :
  Lemma
    (requires i < array_spec_len s)
    (ensures List.Tot.index (array_spec_to_list s) i == array_spec_idx s i)
    [SMTPat (List.Tot.index (array_spec_to_list s) i)]
assume val array_spec_to_list_of_list #a (xs: list a) :
  Lemma (array_spec_to_list (array_spec_of_list xs) == xs)
    [SMTPat (array_spec_to_list (array_spec_of_list xs))]

let is_sorted_array_spec_to_list_of_list #xs (h: is_sorted xs) :
  is_sorted (array_spec_to_list (array_spec_of_list xs)) = ()

let is_sorted_cons_cons (#x #y: Int32.t) #xs
    (h1: is_sorted (y::xs))
    (h2: (Int32.v x <= Int32.v y))
    : is_sorted (x::y::xs) =
  admit ()

let is_sorted_singleton (#x: Int32.t) : is_sorted [x] = ()

open FStar.Tactics.V2
let tac () : Tac unit =
  apply (`is_sorted_array_spec_to_list_of_list);
  repeat' (fun _ -> apply (`is_sorted_cons_cons));
  apply (`is_sorted_singleton)

#set-options "--no_smt"
let my_array_sorted () : is_sorted (array_spec_to_list Global_my_array.var_my_array) =
  _ by (tac ())