module SwitchModel

open Pulse

#lang-pulse

(* Two states of one resource: every case of the switch moves it on. *)
let before (x: int) : slprop = emp
let after (x: int) : slprop = emp

ghost fn start (x: int)
  ensures before x
{
  fold (before x);
}

ghost fn step (x: int)
  requires before x
  ensures after x
{
  unfold (before x);
  fold (after x);
}

ghost fn drop_before (x: int)
  requires before x
{
  unfold (before x);
}

ghost fn drop_after (x: int)
  requires after x
{
  unfold (after x);
}
