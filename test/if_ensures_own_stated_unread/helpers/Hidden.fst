module Hidden

open Pulse

#lang-pulse

(* A resource folded away under a name the frame cannot see through. *)
let hide (s: slprop) : slprop = s

ghost fn hide_it (s: slprop)
  requires s
  ensures hide s
{
  fold (hide s);
}

ghost fn show_it (s: slprop)
  requires hide s
  ensures s
{
  unfold (hide s);
}
