module Pulse.Lib.C.UInt16

include FStar.UInt16
module U16 = FStar.UInt16

/// Wrapping (modular) arithmetic for unsigned C semantics: these are total
/// (no overflow precondition). The postcondition is exact when the result
/// fits and the wrapped value otherwise, so non-overflowing uses keep the
/// natural `v z == v x + v y` reasoning.
let add_wrap (x y: U16.t)
  : Pure U16.t
    (requires True)
    (ensures fun z ->
      if FStar.UInt.fits (U16.v x + U16.v y) U16.n
      then U16.v z == U16.v x + U16.v y
      else U16.v z == FStar.UInt.add_mod (U16.v x) (U16.v y))
  = U16.add_mod x y

let sub_wrap (x y: U16.t)
  : Pure U16.t
    (requires True)
    (ensures fun z ->
      if FStar.UInt.fits (U16.v x - U16.v y) U16.n
      then U16.v z == U16.v x - U16.v y
      else U16.v z == FStar.UInt.sub_mod (U16.v x) (U16.v y))
  = U16.sub_mod x y

let mul_wrap (x y: U16.t)
  : Pure U16.t
    (requires True)
    (ensures fun z ->
      if FStar.UInt.fits (U16.v x * U16.v y) U16.n
      then U16.v z == U16.v x * U16.v y
      else U16.v z == FStar.UInt.mul_mod (U16.v x) (U16.v y))
  = U16.mul_mod x y
