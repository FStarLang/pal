module Pulse.Lib.C.SizeT

(* C's operators on `size_t`, which is unsigned and pointer-sized: arithmetic
   wraps modulo `Target.addr_limit` and the bitwise operators act on
   `8 * Target.ptr_bytes` bits. `FStar.SizeT` has only the checked arithmetic
   and no bitwise operators at all, so these go through the mathematical
   integer, as `Pulse.Lib.C.UInt64` does for the fixed-width types. The
   postconditions of the wrapping operators are exact when the result fits,
   so code that never wraps keeps the natural `v z == v x + v y` reasoning. *)

module SZ = FStar.SizeT
module U32 = FStar.UInt32
module UI = FStar.UInt
module T = Pulse.Lib.C.Palow.Target
module CT = Pulse.Lib.C.Palow.CTypes

let width : n:pos { n == 8 * T.ptr_bytes } = 8 * T.ptr_bytes

let max : n:nat { n == T.addr_limit - 1 } = T.addr_limit - 1

let bits (x: SZ.t) : UI.uint_t width =
  T.addr_limit_pow2 ();
  SZ.v x

let of_bits (x: UI.uint_t width) : y:SZ.t { SZ.v y == x } =
  T.addr_limit_pow2 ();
  CT.size_t_fits x;
  SZ.uint_to_t x

let add_wrap (x y: SZ.t)
  : Pure SZ.t
    (requires True)
    (ensures fun z ->
      if SZ.v x + SZ.v y < T.addr_limit
      then SZ.v z == SZ.v x + SZ.v y
      else SZ.v z == SZ.v x + SZ.v y - T.addr_limit)
  = T.addr_limit_pow2 ();
    of_bits (UI.add_mod (bits x) (bits y))

let sub_wrap (x y: SZ.t)
  : Pure SZ.t
    (requires True)
    (ensures fun z ->
      if SZ.v x >= SZ.v y
      then SZ.v z == SZ.v x - SZ.v y
      else SZ.v z == SZ.v x - SZ.v y + T.addr_limit)
  = T.addr_limit_pow2 ();
    of_bits (UI.sub_mod (bits x) (bits y))

let mul_wrap (x y: SZ.t)
  : Pure SZ.t
    (requires True)
    (ensures fun z ->
      SZ.v z == (SZ.v x * SZ.v y) % T.addr_limit /\
      (SZ.v x * SZ.v y < T.addr_limit ==> SZ.v z == SZ.v x * SZ.v y))
  = T.addr_limit_pow2 ();
    of_bits (UI.mul_mod (bits x) (bits y))

let logand (x y: SZ.t)
  : Pure SZ.t (requires True)
    (ensures fun z ->
      SZ.v z == UI.logand (bits x) (bits y) /\ SZ.v z <= SZ.v x /\ SZ.v z <= SZ.v y)
  = UI.logand_le (bits x) (bits y);
    of_bits (UI.logand (bits x) (bits y))

let logor (x y: SZ.t)
  : Pure SZ.t (requires True)
    (ensures fun z ->
      SZ.v z == UI.logor (bits x) (bits y) /\ SZ.v z >= SZ.v x /\ SZ.v z >= SZ.v y)
  = UI.logor_ge (bits x) (bits y);
    of_bits (UI.logor (bits x) (bits y))

let logxor (x y: SZ.t)
  : Pure SZ.t (requires True) (ensures fun z -> SZ.v z == UI.logxor (bits x) (bits y))
  = of_bits (UI.logxor (bits x) (bits y))

(* `~x`, stated as the subtraction it equals, which the solver can reason
   about where it cannot about `lognot`. *)
let lognot (x: SZ.t)
  : Pure SZ.t (requires True) (ensures fun z -> SZ.v z == max - SZ.v x)
  = of_bits (max - SZ.v x)

let lognot_spec (x: SZ.t) : Lemma (SZ.v (lognot x) == UI.lognot (bits x)) =
  T.addr_limit_pow2 ();
  UI.lemma_lognot_value (bits x)

let shift_left (x: SZ.t) (s: U32.t)
  : Pure SZ.t
    (requires U32.v s < width)
    (ensures fun z ->
      SZ.v z == (SZ.v x * pow2 (U32.v s)) % T.addr_limit /\
      (SZ.v x * pow2 (U32.v s) < T.addr_limit ==> SZ.v z == SZ.v x * pow2 (U32.v s)))
  = T.addr_limit_pow2 ();
    of_bits (UI.shift_left (bits x) (U32.v s))

let shift_right (x: SZ.t) (s: U32.t)
  : Pure SZ.t
    (requires U32.v s < width)
    (ensures fun z -> SZ.v z == SZ.v x / pow2 (U32.v s))
  = of_bits (UI.shift_right (bits x) (U32.v s))
