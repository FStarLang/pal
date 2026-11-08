module Pulse.Lib.C.Palow.Target

(* Any concrete choice will do: this only shows that the interface can be
   met. Clients see `Target.fsti`, where it is abstract. *)
let little_endian = true
let ptr_64 = true
let max_align = 16sz
