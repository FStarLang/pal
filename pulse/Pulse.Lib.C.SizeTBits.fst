module Pulse.Lib.C.SizeTBits
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64
open Pulse.Lib.C.Assumptions

/// Bitwise operators on size_t. FStar.SizeT has none, and their C meaning
/// depends on the width of size_t (`~x` in particular), so they are defined
/// through uint64_t under Pulse.Lib.C.Assumptions' 64-bit size_t model.
/// `v64 x` is `SZ.v x` at the type the FStar.UInt lemmas expect, so the
/// postconditions read exactly like those of FStar.UInt64's operators.
let v64 (x: SZ.t) : FStar.UInt.uint_t 64 =
  sizet_v_lt_pow2_64 x;
  SZ.v x

let to_u64 (x: SZ.t) : Pure U64.t (requires True) (ensures fun y -> U64.v y == v64 x) =
  sizet_v_lt_pow2_64 x;
  FStar.Math.Lemmas.small_mod (SZ.v x) (pow2 64);
  SZ.sizet_to_uint64 x

let of_u64 (x: U64.t) : Pure SZ.t (requires True) (ensures fun y -> v64 y == U64.v x) =
  SZ.uint64_to_sizet x

let logand (x y: SZ.t)
  : Pure SZ.t (requires True) (ensures fun z -> v64 z == FStar.UInt.logand (v64 x) (v64 y))
  = of_u64 (U64.logand (to_u64 x) (to_u64 y))

let logor (x y: SZ.t)
  : Pure SZ.t (requires True) (ensures fun z -> v64 z == FStar.UInt.logor (v64 x) (v64 y))
  = of_u64 (U64.logor (to_u64 x) (to_u64 y))

let logxor (x y: SZ.t)
  : Pure SZ.t (requires True) (ensures fun z -> v64 z == FStar.UInt.logxor (v64 x) (v64 y))
  = of_u64 (U64.logxor (to_u64 x) (to_u64 y))

let lognot (x: SZ.t)
  : Pure SZ.t (requires True) (ensures fun z -> v64 z == FStar.UInt.lognot (v64 x))
  = of_u64 (U64.lognot (to_u64 x))

let shift_left (x: SZ.t) (s: U32.t{U32.v s < 64})
  : Pure SZ.t (requires True)
      (ensures fun z -> SZ.v z == (SZ.v x * pow2 (U32.v s)) % pow2 64)
  = of_u64 (U64.shift_left (to_u64 x) s)

let shift_right (x: SZ.t) (s: U32.t{U32.v s < 64})
  : Pure SZ.t (requires True)
      (ensures fun z -> SZ.v z == SZ.v x / pow2 (U32.v s))
  = of_u64 (U64.shift_right (to_u64 x) s)
