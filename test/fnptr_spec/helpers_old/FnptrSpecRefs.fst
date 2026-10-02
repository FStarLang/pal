module FnptrSpecRefs

(* The ownership of a `_plain` parameter, in the current memory model.

   `_plain` says the translation grants nothing, so a contract that wants the
   pointee has to name the ownership itself -- and the two memory models spell
   that differently: a reference and its `pts_to` here, an address and a
   per-type points-to in Palow. Naming it once, here, keeps the C the same
   under both; see `helpers_palow/FnptrSpecRefs.fst` for the other half.

   `unfold` matters: Pulse's matcher has to see straight through to the
   concrete slprop for the call site to line up with the callee's contract. *)

open Pulse.Lib.Pervasives
module T = Typedef_int32_t

unfold let plain_pts_to (q: ref T.ty_int32_t) (v: T.ty_int32_t) : slprop =
  Pulse.Lib.Reference.pts_to q #1.0R v
