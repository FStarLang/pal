module Pulse.Lib.C.Palow.Held
#lang-pulse
open Pulse

let held (p: slprop) : slprop = p

ghost fn hold (p: slprop)
  requires p
  ensures  held p
{
  fold (held p)
}

ghost fn unhold (p: slprop)
  requires held p
  ensures  p
{
  unfold (held p)
}
