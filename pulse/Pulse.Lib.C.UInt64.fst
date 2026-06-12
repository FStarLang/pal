module Pulse.Lib.C.UInt64

include FStar.UInt64
module U64 = FStar.UInt64

/// Wrapping (modular) arithmetic for unsigned C semantics: these are total
/// (no overflow precondition). The postcondition is exact when the result
/// fits and the wrapped value otherwise, so non-overflowing uses keep the
/// natural `v z == v x + v y` reasoning.
let add_wrap (x y: U64.t)
  : Pure U64.t
    (requires True)
    (ensures fun z ->
      if FStar.UInt.fits (U64.v x + U64.v y) U64.n
      then U64.v z == U64.v x + U64.v y
      else U64.v z == FStar.UInt.add_mod (U64.v x) (U64.v y))
  = U64.add_mod x y

let sub_wrap (x y: U64.t)
  : Pure U64.t
    (requires True)
    (ensures fun z ->
      if FStar.UInt.fits (U64.v x - U64.v y) U64.n
      then U64.v z == U64.v x - U64.v y
      else U64.v z == FStar.UInt.sub_mod (U64.v x) (U64.v y))
  = U64.sub_mod x y

let mul_wrap (x y: U64.t)
  : Pure U64.t
    (requires True)
    (ensures fun z ->
      if FStar.UInt.fits (U64.v x * U64.v y) U64.n
      then U64.v z == U64.v x * U64.v y
      else U64.v z == FStar.UInt.mul_mod (U64.v x) (U64.v y))
  = U64.mul_mod x y
