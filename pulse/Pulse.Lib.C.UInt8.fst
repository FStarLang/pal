module Pulse.Lib.C.UInt8

include FStar.UInt8
module U8 = FStar.UInt8

/// Wrapping (modular) arithmetic for unsigned C semantics: these are total
/// (no overflow precondition). The postcondition is exact when the result
/// fits and the wrapped value otherwise, so non-overflowing uses keep the
/// natural `v z == v x + v y` reasoning.
let add_wrap (x y: U8.t)
  : Pure U8.t
    (requires True)
    (ensures fun z ->
      if FStar.UInt.fits (U8.v x + U8.v y) U8.n
      then U8.v z == U8.v x + U8.v y
      else U8.v z == FStar.UInt.add_mod (U8.v x) (U8.v y))
  = U8.add_mod x y

let sub_wrap (x y: U8.t)
  : Pure U8.t
    (requires True)
    (ensures fun z ->
      if FStar.UInt.fits (U8.v x - U8.v y) U8.n
      then U8.v z == U8.v x - U8.v y
      else U8.v z == FStar.UInt.sub_mod (U8.v x) (U8.v y))
  = U8.sub_mod x y

let mul_wrap (x y: U8.t)
  : Pure U8.t
    (requires True)
    (ensures fun z ->
      if FStar.UInt.fits (U8.v x * U8.v y) U8.n
      then U8.v z == U8.v x * U8.v y
      else U8.v z == FStar.UInt.mul_mod (U8.v x) (U8.v y))
  = U8.mul_mod x y
