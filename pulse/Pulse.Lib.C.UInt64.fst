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

/// Byte reversal, for `__builtin_bswap64`.
///
/// A definition, not an axiom: the builtin's meaning is entirely captured by
/// the shifts and masks below, so nothing new is assumed and the result can be
/// reasoned about to whatever depth a caller needs by unfolding it. FunOS
/// reaches this through its big-endian hardware descriptors.
let bswap64 (x: U64.t) : U64.t =
  U64.logor
    (U64.logor
      (U64.logor
        (U64.shift_left (U64.logand x 0xFFuL) 56ul)
        (U64.shift_left (U64.logand (U64.shift_right x 8ul) 0xFFuL) 48ul))
      (U64.logor
        (U64.shift_left (U64.logand (U64.shift_right x 16ul) 0xFFuL) 40ul)
        (U64.shift_left (U64.logand (U64.shift_right x 24ul) 0xFFuL) 32ul)))
    (U64.logor
      (U64.logor
        (U64.shift_left (U64.logand (U64.shift_right x 32ul) 0xFFuL) 24ul)
        (U64.shift_left (U64.logand (U64.shift_right x 40ul) 0xFFuL) 16ul))
      (U64.logor
        (U64.shift_left (U64.logand (U64.shift_right x 48ul) 0xFFuL) 8ul)
        (U64.logand (U64.shift_right x 56ul) 0xFFuL)))
