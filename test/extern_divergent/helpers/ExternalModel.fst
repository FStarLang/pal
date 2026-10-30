module ExternalModel

open Pulse
module U32 = FStar.UInt32

#lang-pulse

let same_type (#t: Type) (declaration implementation: t) : unit = ()

fn total_implementation (n: U32.t)
  requires emp
  returns result: U32.t
  ensures pure (U32.v result == U32.v n)
{
  n
}

divergent fn implementation (n: U32.t)
  requires emp
  returns result: U32.t
  ensures pure (U32.v result == U32.v n)
{
  n
}
