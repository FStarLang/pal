module Helper
open Pulse.Lib.C.Array

let is_sorted (xs: list Int32.t) =
  forall (i j: nat). i < j /\ j < List.length xs ==>
    Int32.v (List.Tot.index xs i) <= Int32.v (List.Tot.index xs j)

let is_sorted_array_spec_to_list_of_list #xs (h: is_sorted xs) :
  is_sorted (array_spec_to_list (array_spec_of_list xs)) = ()

let is_sorted_cons_cons (#x #y: Int32.t) #xs
    (h1: is_sorted (y::xs))
    (h2: (Int32.v x <= Int32.v y))
    : is_sorted (x::y::xs) =
  ()

let is_sorted_singleton (#x: Int32.t) : is_sorted [x] = ()

let rec compute_sorted (xs: list Int32.t) : b:bool { b ==> is_sorted xs } =
  match xs with
  | x::y::xs -> Int32.v x <= Int32.v y && compute_sorted (y::xs)
  | _ -> true

let is_sorted_of_compute_sorted #xs (h: compute_sorted xs) : is_sorted xs = ()

open FStar.Tactics.V2
let prove_by_apply () : Tac unit = // very slow
  apply (`is_sorted_array_spec_to_list_of_list);
  repeat' (fun _ -> apply (`is_sorted_cons_cons));
  apply (`is_sorted_singleton)

let prove_by_norm () : Tac unit =
  apply (`is_sorted_array_spec_to_list_of_list);
  apply (`is_sorted_of_compute_sorted);
  compute ()

#set-options "--no_smt"
let my_array_sorted () : is_sorted (array_spec_to_list Global_my_array.var_my_array) =
  _ by (prove_by_norm ())