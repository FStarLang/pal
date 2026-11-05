module Pulse.Lib.C.Palow.Checked

open Pulse
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.Machine
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast
module Math = FStar.Math.Lemmas

#lang-pulse
#set-options "--z3rlimit 10"

let product_exceeds_limit (a limit: nat) (b: pos)
  : Lemma ((a > limit / b) <==> (a * b > limit)) =
  Math.division_propriety limit b;
  if a > limit / b then
    Math.multiplication_order_lemma a (limit / b + 1) b
  else
    Math.multiplication_order_lemma (limit / b) a b

let mul_u64_u32 (a b: U64.t)
  : Pure (bool & U32.t)
      (requires True)
      (ensures fun pair ->
        let overflow, result = pair in
        U32.v result == (U64.v a * U64.v b) % pow2 32 /\
        (overflow <==> U64.v a * U64.v b >= pow2 32)) =
  let product = U64.mul_mod a b in
  let result = Cast.uint64_to_uint32 product in
  Math.pow2_modulo_modulo_lemma_1 (U64.v a * U64.v b) 32 64;
  if U64.eq b 0uL then false, result
  else
    let limit = U64.div 0xffffffffuL b in
    product_exceeds_limit (U64.v a) 0xffffffff (U64.v b);
    U64.lt limit a, result

fn mul_overflow_u64_u32 (a b: U64.t) (output: ptr)
  requires uint32_t_pts_to_uninit output
  returns overflow: bool
  ensures exists* result.
    uint32_t_pts_to output 1.0R result **
    pure (U32.v result == (U64.v a * U64.v b) % pow2 32 /\
      (overflow <==> U64.v a * U64.v b >= pow2 32))
{
  let overflow, result = mul_u64_u32 a b;
  uint32_t_write_uninit output result;
  overflow
}
