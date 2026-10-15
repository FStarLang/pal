module FnptrSpecRefs

(* The ownership of a `_plain` parameter, in the Palow memory model. See
   `helpers/FnptrSpecRefs.fst` for why this is a helper and not written in the
   C directly. *)

open Pulse.Lib.Pervasives
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow.CTypes
module Int32 = FStar.Int32

unfold let plain_pts_to (q: ptr) (v: Int32.t) : slprop =
  int32_t_pts_to q 1.0R v
