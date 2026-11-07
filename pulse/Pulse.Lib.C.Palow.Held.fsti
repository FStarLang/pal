module Pulse.Lib.C.Palow.Held
(* ---------------------------------------------------------------------------
   Ownership put away

   `held p` is `p`, under a name the prover does not see through. A `const`
   local keeps half of its points-to here once it has been initialised: the
   half left in plain sight is enough to read the object and not enough to
   write it, which is 6.7.3p6 -- an attempt to modify an object defined with a
   const-qualified type is undefined -- and the end of the object's lifetime
   takes the half back to give the storage up.
   --------------------------------------------------------------------------- *)
#lang-pulse
open Pulse

val held (p: slprop) : slprop

ghost fn hold (p: slprop)
  requires p
  ensures  held p

ghost fn unhold (p: slprop)
  requires held p
  ensures  p
