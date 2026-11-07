module Pulse.Lib.C.Palow.Bytes

(* Allocation ids are just naturals in the model; the interface keeps this
   hidden so that no client can invent one or reason about their order. *)
let alloc_id = nat
