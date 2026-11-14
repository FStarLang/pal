module TokModel

open Pulse

#lang-pulse

(* A token about a value, matched by its argument like any handler's state. *)
let tok (#a: Type) (x: a) : slprop = emp
