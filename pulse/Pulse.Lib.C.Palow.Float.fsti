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

val float64_of_float32_injective (x y: float32)
  : Lemma (requires float64_of_float32 x == float64_of_float32 y)
          (ensures  x == y)
