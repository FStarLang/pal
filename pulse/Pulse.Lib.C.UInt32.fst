module Pulse.Lib.C.UInt32

include FStar.UInt32
module U32 = FStar.UInt32

let uint32 = U32.t
let as_int (x: U32.t) : int = U32.v x
let fits (op : int -> int -> int) (vx vy : int) : prop =
  U32.fits (op vx vy)
let min_uint32 = FStar.UInt.min_int U32.n
let max_uint32 = FStar.UInt.max_int U32.n
let (+^) = FStar.UInt32.add

/// Wrapping (modular) arithmetic for unsigned C semantics: these are total
/// (no overflow precondition). The postcondition is exact when the result
/// fits and the wrapped value otherwise, so non-overflowing uses keep the
/// natural `v z == v x + v y` reasoning.
let add_wrap (x y: U32.t)
  : Pure U32.t
    (requires True)
    (ensures fun z ->
      if FStar.UInt.fits (U32.v x + U32.v y) U32.n
      then U32.v z == U32.v x + U32.v y
      else U32.v z == FStar.UInt.add_mod (U32.v x) (U32.v y))
  = U32.add_mod x y

let sub_wrap (x y: U32.t)
  : Pure U32.t
    (requires True)
    (ensures fun z ->
      if FStar.UInt.fits (U32.v x - U32.v y) U32.n
      then U32.v z == U32.v x - U32.v y
      else U32.v z == FStar.UInt.sub_mod (U32.v x) (U32.v y))
  = U32.sub_mod x y

let mul_wrap (x y: U32.t)
  : Pure U32.t
    (requires True)
    (ensures fun z ->
      if FStar.UInt.fits (U32.v x * U32.v y) U32.n
      then U32.v z == U32.v x * U32.v y
      else U32.v z == FStar.UInt.mul_mod (U32.v x) (U32.v y))
  = U32.mul_mod x y

/// `x & 1 == x % 2` for `uint32` -- the common C parity idiom.
let logand_one_is_mod2 (x: U32.t)
  : Lemma (U32.v (U32.logand x 1ul) == U32.v x % 2)
  = FStar.UInt.logand_mask #32 (U32.v x) 1

instance inhabited_uint32 : Pulse.Lib.C.Inhabited.inhabited uint32 = {
  witness = U32.zero
}