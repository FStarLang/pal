module Opaque_ops
#lang-pulse
open Pulse

(* `reveal_opaque` states its fact through the normaliser, so it is proved in
   F*, where that runs, and handed to Pulse as a ghost function. *)
let k_is_four_lemma () : Lemma (Global_opaque_ops.var_opaque_ops.Struct_ops.fld_k == 4l) =
  reveal_opaque (`%Global_opaque_ops.var_opaque_ops) Global_opaque_ops.var_opaque_ops

ghost fn k_is_four (_: unit)
  requires emp
  ensures pure (Global_opaque_ops.var_opaque_ops.Struct_ops.fld_k == 4l)
{
  k_is_four_lemma ();
  ()
}
