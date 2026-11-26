module Pulse.Lib.C.Palow.CheckedWide

open Pulse
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes
open Pulse.Lib.C.Palow.Machine
module U64 = FStar.UInt64
module Math = FStar.Math.Lemmas

#lang-pulse
#set-options "--z3rlimit 10"

(* `__builtin_mul_overflow` into a 64-bit unsigned destination, as
   `Pulse.Lib.C.Palow.Checked.mul_overflow_u64_u32` does into a 32-bit one:
   the destination receives the product modulo 2^64, and the result says
   whether the mathematical product does not fit. A definition, not an
   assumption. *)
let mul_u64_u64 (a b: U64.t)
  : Pure (bool & U64.t)
      (requires True)
      (ensures fun pair ->
        let overflow, result = pair in
        U64.v result == (U64.v a * U64.v b) % pow2 64 /\
        (overflow <==> U64.v a * U64.v b >= pow2 64)) =
  let result = U64.mul_mod a b in
  if U64.eq b 0uL then false, result
  else
    let limit = U64.div 0xffffffffffffffffuL b in
    Pulse.Lib.C.Palow.Checked.product_exceeds_limit (U64.v a) 0xffffffffffffffff (U64.v b);
    U64.lt limit a, result

fn mul_overflow_u64_u64 (a b: U64.t) (output: ptr)
  requires uint64_t_pts_to_uninit output
  returns overflow: bool
  ensures exists* result.
    uint64_t_pts_to output 1.0R result **
    pure (U64.v result == (U64.v a * U64.v b) % pow2 64 /\
      (overflow <==> U64.v a * U64.v b >= pow2 64))
{
  let overflow, result = mul_u64_u64 a b;
  uint64_t_write_uninit output result;
  overflow
}
