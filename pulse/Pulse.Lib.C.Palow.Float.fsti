module Pulse.Lib.C.Palow.Float

(* ---------------------------------------------------------------------------
   The object representation of a C floating-point value.

   F* already has `FStar.Float32.t` and `FStar.Float64.t` with arithmetic and
   comparison on them, and that is all the arithmetic Palow needs -- a C
   `double` is exactly an IEEE-754 binary64 and F* says so. What F* does *not*
   say is what a `double` looks like in memory, and that is the one thing a
   byte-level memory model cannot do without: `float_pair.d` is four bytes on
   from `float_pair.f`, and the eight bytes it occupies are an object like any
   other.

   So this module adds exactly one thing per width: an injective map from a
   value to its `w`-bit object representation. Everything else -- the
   points-to, the `_repr` relation, the eight resource lemmas, reads and
   writes, arrays of floats, floats as struct fields -- is then the ordinary
   scalar construction in `Pulse.Lib.C.Palow.CTypes`, with `float32_bits` in
   the place `Encoding.to_bits` occupies for a signed integer.

   Injectivity is the modelling assumption, and it is the right one: C says
   distinct object representations are distinct values, and the cases where
   this bites -- `+0.0` against `-0.0`, one NaN payload against another -- are
   cases where C likewise keeps the two apart as objects. What it does *not*
   claim is the converse: nothing here says that every `w`-bit pattern is a
   value, because C does not say that either (a trap representation is
   allowed), and no part of Palow needs it.

   This interface is axiomatized: there is no `.fst`. It has to be its own
   module for exactly that reason -- `CTypes` has an implementation, so it
   cannot host an assumption.
   --------------------------------------------------------------------------- *)

module F32 = FStar.Float32
module F64 = FStar.Float64

let float32 = F32.t
let float64 = F64.t

(* The object representation, as the natural number its bits spell. *)
val float32_bits (x: float32) : n:nat { n < pow2 32 }
val float64_bits (x: float64) : n:nat { n < pow2 64 }

val float32_bits_injective (x y: float32)
  : Lemma (requires float32_bits x == float32_bits y)
          (ensures  x == y)

val float64_bits_injective (x y: float64)
  : Lemma (requires float64_bits x == float64_bits y)
          (ensures  x == y)

(* Conversion between the two widths. C's `(double) f` is exact and `(float) d`
   rounds, so only one direction has an inverse, and only that direction is
   stated. Without these a widening conversion would have to go through an
   integer, which is not what C does. *)
val float64_of_float32 (x: float32) : float64
val float32_of_float64 (x: float64) : float32

(* Conversion from a `uint64_t`. F* only has `of_int` from an `Int64.t`, which
   covers every C integer type but this one: the values from 2^63 up have no
   `Int64.t`, and reaching `of_int` through `uint64_to_int64` would wrap them
   to negative numbers, which C's `(double) u` does not do (6.3.1.4p2). Below
   2^63 the two agree, and that is all that is said about them. *)
val float64_of_uint64 (x: FStar.UInt64.t) : float64
val float32_of_uint64 (x: FStar.UInt64.t) : float32

val float64_of_uint64_small (x: FStar.UInt64.t)
  : Lemma (requires FStar.UInt64.v x < pow2 63)
          (ensures  float64_of_uint64 x == F64.of_int (FStar.Int64.int_to_t (FStar.UInt64.v x)))

val float32_of_uint64_small (x: FStar.UInt64.t)
  : Lemma (requires FStar.UInt64.v x < pow2 63)
          (ensures  float32_of_uint64 x == F32.of_int (FStar.Int64.int_to_t (FStar.UInt64.v x)))

val float64_of_float32_injective (x y: float32)
  : Lemma (requires float64_of_float32 x == float64_of_float32 y)
          (ensures  x == y)

(* Conversion to an integer type. C truncates toward zero, and only when the
   truncated value is representable in the target type; otherwise the
   behaviour is undefined (6.3.1.4p1), which covers NaN and the infinities
   too. So the range is not a property of the result but a precondition of
   the conversion, stated -- as C states it -- by comparing the float itself
   with mathematical integers: the value must lie strictly between `lo - 1`
   and `hi + 1`.

   `lt_int` and `gt_int` are exact comparisons with an `int`, not
   comparisons with a rounded float, and both are false for a NaN. They,
   `trunc`, and the one axiom relating them are all this says: like the rest
   of floating point here, they have no model beyond that, so a program can
   only meet the precondition with facts about the float it got elsewhere. *)
val float64_lt_int (x: float64) (n: int) : bool
val float64_gt_int (x: float64) (n: int) : bool
val float32_lt_int (x: float32) (n: int) : bool
val float32_gt_int (x: float32) (n: int) : bool

let float64_fits (x: float64) (lo hi: int) : bool =
  float64_gt_int x (lo - 1) && float64_lt_int x (hi + 1)
let float32_fits (x: float32) (lo hi: int) : bool =
  float32_gt_int x (lo - 1) && float32_lt_int x (hi + 1)

(* The integer part, rounding toward zero. Meaningless outside the range
   where some `fits` holds, and nothing is said about it there. *)
val float64_trunc (x: float64) : int
val float32_trunc (x: float32) : int

val float64_trunc_bounds (x: float64) (lo hi: int)
  : Lemma (requires float64_fits x lo hi)
          (ensures  lo <= float64_trunc x /\ float64_trunc x <= hi)
val float32_trunc_bounds (x: float32) (lo hi: int)
  : Lemma (requires float32_fits x lo hi)
          (ensures  lo <= float32_trunc x /\ float32_trunc x <= hi)

(* An integer small enough to be exact in the format compares and truncates
   as itself. *)
val float64_lt_int_of_int (n: FStar.Int64.t) (m: int)
  : Lemma (requires -9007199254740992 <= FStar.Int64.v n /\ FStar.Int64.v n <= 9007199254740992)
          (ensures  float64_lt_int (F64.of_int n) m <==> FStar.Int64.v n < m)
          [SMTPat (float64_lt_int (F64.of_int n) m)]
val float64_gt_int_of_int (n: FStar.Int64.t) (m: int)
  : Lemma (requires -9007199254740992 <= FStar.Int64.v n /\ FStar.Int64.v n <= 9007199254740992)
          (ensures  float64_gt_int (F64.of_int n) m <==> FStar.Int64.v n > m)
          [SMTPat (float64_gt_int (F64.of_int n) m)]
val float64_trunc_of_int (n: FStar.Int64.t)
  : Lemma (requires -9007199254740992 <= FStar.Int64.v n /\ FStar.Int64.v n <= 9007199254740992)
          (ensures  float64_trunc (F64.of_int n) == FStar.Int64.v n)
          [SMTPat (float64_trunc (F64.of_int n))]
val float32_lt_int_of_int (n: FStar.Int64.t) (m: int)
  : Lemma (requires -16777216 <= FStar.Int64.v n /\ FStar.Int64.v n <= 16777216)
          (ensures  float32_lt_int (F32.of_int n) m <==> FStar.Int64.v n < m)
          [SMTPat (float32_lt_int (F32.of_int n) m)]
val float32_gt_int_of_int (n: FStar.Int64.t) (m: int)
  : Lemma (requires -16777216 <= FStar.Int64.v n /\ FStar.Int64.v n <= 16777216)
          (ensures  float32_gt_int (F32.of_int n) m <==> FStar.Int64.v n > m)
          [SMTPat (float32_gt_int (F32.of_int n) m)]
val float32_trunc_of_int (n: FStar.Int64.t)
  : Lemma (requires -16777216 <= FStar.Int64.v n /\ FStar.Int64.v n <= 16777216)
          (ensures  float32_trunc (F32.of_int n) == FStar.Int64.v n)
          [SMTPat (float32_trunc (F32.of_int n))]

let float32_to_int8 (x: float32 { float32_fits x (-128) 127 }) : FStar.Int8.t =
  float32_trunc_bounds x (-128) 127;
  FStar.Int8.int_to_t (float32_trunc x)

let float32_to_int16 (x: float32 { float32_fits x (-32768) 32767 }) : FStar.Int16.t =
  float32_trunc_bounds x (-32768) 32767;
  FStar.Int16.int_to_t (float32_trunc x)

let float32_to_int32 (x: float32 { float32_fits x (-2147483648) 2147483647 }) : FStar.Int32.t =
  float32_trunc_bounds x (-2147483648) 2147483647;
  FStar.Int32.int_to_t (float32_trunc x)

let float32_to_int64 (x: float32 { float32_fits x (-9223372036854775808) 9223372036854775807 }) : FStar.Int64.t =
  float32_trunc_bounds x (-9223372036854775808) 9223372036854775807;
  FStar.Int64.int_to_t (float32_trunc x)

let float32_to_uint8 (x: float32 { float32_fits x 0 255 }) : FStar.UInt8.t =
  float32_trunc_bounds x 0 255;
  FStar.UInt8.uint_to_t (float32_trunc x)

let float32_to_uint16 (x: float32 { float32_fits x 0 65535 }) : FStar.UInt16.t =
  float32_trunc_bounds x 0 65535;
  FStar.UInt16.uint_to_t (float32_trunc x)

let float32_to_uint32 (x: float32 { float32_fits x 0 4294967295 }) : FStar.UInt32.t =
  float32_trunc_bounds x 0 4294967295;
  FStar.UInt32.uint_to_t (float32_trunc x)

let float32_to_uint64 (x: float32 { float32_fits x 0 18446744073709551615 }) : FStar.UInt64.t =
  float32_trunc_bounds x 0 18446744073709551615;
  FStar.UInt64.uint_to_t (float32_trunc x)

let float64_to_int8 (x: float64 { float64_fits x (-128) 127 }) : FStar.Int8.t =
  float64_trunc_bounds x (-128) 127;
  FStar.Int8.int_to_t (float64_trunc x)

let float64_to_int16 (x: float64 { float64_fits x (-32768) 32767 }) : FStar.Int16.t =
  float64_trunc_bounds x (-32768) 32767;
  FStar.Int16.int_to_t (float64_trunc x)

let float64_to_int32 (x: float64 { float64_fits x (-2147483648) 2147483647 }) : FStar.Int32.t =
  float64_trunc_bounds x (-2147483648) 2147483647;
  FStar.Int32.int_to_t (float64_trunc x)

let float64_to_int64 (x: float64 { float64_fits x (-9223372036854775808) 9223372036854775807 }) : FStar.Int64.t =
  float64_trunc_bounds x (-9223372036854775808) 9223372036854775807;
  FStar.Int64.int_to_t (float64_trunc x)

let float64_to_uint8 (x: float64 { float64_fits x 0 255 }) : FStar.UInt8.t =
  float64_trunc_bounds x 0 255;
  FStar.UInt8.uint_to_t (float64_trunc x)

let float64_to_uint16 (x: float64 { float64_fits x 0 65535 }) : FStar.UInt16.t =
  float64_trunc_bounds x 0 65535;
  FStar.UInt16.uint_to_t (float64_trunc x)

let float64_to_uint32 (x: float64 { float64_fits x 0 4294967295 }) : FStar.UInt32.t =
  float64_trunc_bounds x 0 4294967295;
  FStar.UInt32.uint_to_t (float64_trunc x)

let float64_to_uint64 (x: float64 { float64_fits x 0 18446744073709551615 }) : FStar.UInt64.t =
  float64_trunc_bounds x 0 18446744073709551615;
  FStar.UInt64.uint_to_t (float64_trunc x)

(* ---------------------------------------------------------------------------
   The value of a float, for proofs. Everything above treats a float as an
   opaque bit pattern; a program that needs to know *which* number it holds --
   to discharge a conversion's range, say -- needs a little more, and this is
   that little, stated so that each axiom is true of IEEE-754 binary32 and
   binary64 with round-to-nearest:

   - `value` is the real number a finite float denotes, and `None` for a NaN
     or an infinity.
   - A C literal is `float{w}_lit s num den k`: the literal whose source text is
     `s`, which the translator has already rounded to `num / den` with
     `den = 2^k`. The string is only the label extraction would print; the
     facts come from `num`, `den` and `k`, and are only claimed when they
     describe a representable value. `of_literal s` itself is left alone:
     giving it a value would let two calls disagree about the same string.
   - `lt`/`lte` agree with the order on values when both are finite, and a
     float between two finite ones is finite.
   - `mul` of two finite floats whose exact product is safely below the
     overflow threshold is finite and within a relative error of half an ulp,
     plus an absolute error for underflow; the absolute term is stated far
     more loosely than it is, which keeps it a true statement.
   - Comparisons with integers follow from the value.
   --------------------------------------------------------------------------- *)
module R = FStar.Real

let rabs (x: R.real) : R.real = if R.(x >=. zero) then x else R.(zero -. x)

val float64_value (x: float64) : option R.real

let float64_finite (x: float64) : prop = Some? (float64_value x)

let float64_val (x: float64 { float64_finite x }) : R.real = Some?.v (float64_value x)

val float64_lit (s: string) (num: int) (den: pos) (k: nat)
  : x: float64 {
      (den == pow2 k /\ k <= 1074 /\ - 9007199254740992 < num /\ num < 9007199254740992) ==>
      (float64_finite x /\ R.(float64_val x *. of_int den == of_int num))
    }

val float64_of_int_value (n: FStar.Int64.t)
  : Lemma (requires - 9007199254740992 <= FStar.Int64.v n /\ FStar.Int64.v n <= 9007199254740992)
          (ensures  float64_finite (F64.of_int n) /\
                    float64_val (F64.of_int n) == R.of_int (FStar.Int64.v n))
          [SMTPat (F64.of_int n)]

val float64_lte_value (x y: float64)
  : Lemma (requires float64_finite x /\ float64_finite y)
          (ensures  (F64.lte x y <==> R.(float64_val x <=. float64_val y)))
          [SMTPat (F64.lte x y)]

val float64_lt_value (x y: float64)
  : Lemma (requires float64_finite x /\ float64_finite y)
          (ensures  (F64.lt x y <==> R.(float64_val x <. float64_val y)))
          [SMTPat (F64.lt x y)]

val float64_between_finite (a x b: float64)
  : Lemma (requires float64_finite a /\ float64_finite b /\ F64.lte a x /\ F64.lte x b)
          (ensures  float64_finite x)
          [SMTPat (F64.lte a x); SMTPat (F64.lte x b)]

val float64_mul_value (x y: float64)
  : Lemma (requires float64_finite x /\ float64_finite y /\
                    R.(rabs (float64_val x *. float64_val y) <. 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000.0R))
          (ensures  float64_finite (F64.mul x y) /\
                    R.(rabs (float64_val (F64.mul x y) -. float64_val x *. float64_val y)
                       <=. rabs (float64_val x *. float64_val y) *. 0.00000000000000011102230246251565404236316680908203125R +. 0.5R))
          [SMTPat (F64.mul x y)]

val float64_gt_int_value (x: float64) (n: int)
  : Lemma (requires float64_finite x /\ R.(float64_val x >. of_int n))
          (ensures  float64_gt_int x n)
          [SMTPat (float64_gt_int x n)]

val float64_lt_int_value (x: float64) (n: int)
  : Lemma (requires float64_finite x /\ R.(float64_val x <. of_int n))
          (ensures  float64_lt_int x n)
          [SMTPat (float64_lt_int x n)]

val float32_value (x: float32) : option R.real

let float32_finite (x: float32) : prop = Some? (float32_value x)

let float32_val (x: float32 { float32_finite x }) : R.real = Some?.v (float32_value x)

val float32_lit (s: string) (num: int) (den: pos) (k: nat)
  : x: float32 {
      (den == pow2 k /\ k <= 149 /\ - 16777216 < num /\ num < 16777216) ==>
      (float32_finite x /\ R.(float32_val x *. of_int den == of_int num))
    }

val float32_of_int_value (n: FStar.Int64.t)
  : Lemma (requires - 16777216 <= FStar.Int64.v n /\ FStar.Int64.v n <= 16777216)
          (ensures  float32_finite (F32.of_int n) /\
                    float32_val (F32.of_int n) == R.of_int (FStar.Int64.v n))
          [SMTPat (F32.of_int n)]

val float32_lte_value (x y: float32)
  : Lemma (requires float32_finite x /\ float32_finite y)
          (ensures  (F32.lte x y <==> R.(float32_val x <=. float32_val y)))
          [SMTPat (F32.lte x y)]

val float32_lt_value (x y: float32)
  : Lemma (requires float32_finite x /\ float32_finite y)
          (ensures  (F32.lt x y <==> R.(float32_val x <. float32_val y)))
          [SMTPat (F32.lt x y)]

val float32_between_finite (a x b: float32)
  : Lemma (requires float32_finite a /\ float32_finite b /\ F32.lte a x /\ F32.lte x b)
          (ensures  float32_finite x)
          [SMTPat (F32.lte a x); SMTPat (F32.lte x b)]

val float32_mul_value (x y: float32)
  : Lemma (requires float32_finite x /\ float32_finite y /\
                    R.(rabs (float32_val x *. float32_val y) <. 100000000000000000000000000000000000000.0R))
          (ensures  float32_finite (F32.mul x y) /\
                    R.(rabs (float32_val (F32.mul x y) -. float32_val x *. float32_val y)
                       <=. rabs (float32_val x *. float32_val y) *. 0.000000059604644775390625R +. 0.5R))
          [SMTPat (F32.mul x y)]

val float32_gt_int_value (x: float32) (n: int)
  : Lemma (requires float32_finite x /\ R.(float32_val x >. of_int n))
          (ensures  float32_gt_int x n)
          [SMTPat (float32_gt_int x n)]

val float32_lt_int_value (x: float32) (n: int)
  : Lemma (requires float32_finite x /\ R.(float32_val x <. of_int n))
          (ensures  float32_lt_int x n)
          [SMTPat (float32_lt_int x n)]
