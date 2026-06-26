module Pulse.Lib.C
#lang-pulse
include Pulse.Lib.C.Inhabited
include FStar.SizeT // before Int32 to not shadow fits there
include Pulse.Lib.C.Int32
include Pulse.Lib.C.Ref
include Pulse.Lib.C.CoreRef
include Pulse.Lib.C.Array
include Pulse.Class.PtsTo
include FStar.Int.Cast
include Pulse.Lib.C.Casts
include Pulse.Lib.C.UnaryOps
include Pulse.Lib.C.Sizeof
include Pulse.Lib.C.Nullable
include Pulse.Lib.WithPure
open Pulse.Lib.Core
let _Bool = bool

// C `float`/`double` are backed by the upstream IEEE-754 float modules.
let float32 = FStar.Float32.t
let float64 = FStar.Float64.t

let float32_zero : float32 = FStar.Float32.zero
let float64_zero : float64 = FStar.Float64.zero

// C float literals are concrete strings, replaced with the corresponding C
// constant during extraction.
let float32_of_string (s: string) : float32 = FStar.Float32.of_literal s
let float64_of_string (s: string) : float64 = FStar.Float64.of_literal s

// Unary negation: `-x` is `0 - x`.
let float32_neg (x: float32) : float32 = FStar.Float32.sub FStar.Float32.zero x
let float32_add : float32 -> float32 -> float32 = FStar.Float32.add
let float32_sub : float32 -> float32 -> float32 = FStar.Float32.sub
let float32_mul : float32 -> float32 -> float32 = FStar.Float32.mul
let float32_div : float32 -> float32 -> float32 = FStar.Float32.div
// C `==` on floats is IEEE-754 equality (NaN <> NaN, +0.0 == -0.0).
let float32_eq : float32 -> float32 -> bool = FStar.Float32.ieee_eq
let float32_lt : float32 -> float32 -> bool = FStar.Float32.lt
let float32_lte : float32 -> float32 -> bool = FStar.Float32.lte
// C truth value of a float: nonzero is true (so NaN is true, +/-0.0 is false).
let float32_to_bool (x: float32) : bool = not (FStar.Float32.ieee_eq x FStar.Float32.zero)
let float32_of_bool (b: bool) : float32 = if b then FStar.Float32.one else FStar.Float32.zero
// Truncation to / from integers has no upstream realization yet.
val float32_to_int : float32 -> int
val float32_of_int : int -> float32

let float64_neg (x: float64) : float64 = FStar.Float64.sub FStar.Float64.zero x
let float64_add : float64 -> float64 -> float64 = FStar.Float64.add
let float64_sub : float64 -> float64 -> float64 = FStar.Float64.sub
let float64_mul : float64 -> float64 -> float64 = FStar.Float64.mul
let float64_div : float64 -> float64 -> float64 = FStar.Float64.div
let float64_eq : float64 -> float64 -> bool = FStar.Float64.ieee_eq
let float64_lt : float64 -> float64 -> bool = FStar.Float64.lt
let float64_lte : float64 -> float64 -> bool = FStar.Float64.lte
let float64_to_bool (x: float64) : bool = not (FStar.Float64.ieee_eq x FStar.Float64.zero)
let float64_of_bool (b: bool) : float64 = if b then FStar.Float64.one else FStar.Float64.zero
val float64_to_int : float64 -> int
val float64_of_int : int -> float64

instance inhabited_float32 : inhabited float32 = {
  witness = float32_zero
}

instance inhabited_float64 : inhabited float64 = {
  witness = float64_zero
}

instance has_zero_default_float32 : has_zero_default float32 = {
  zero_default = float32_zero
}

instance has_zero_default_float64 : has_zero_default float64 = {
  zero_default = float64_zero
}

// We assume size_t is at least 64 bits.
assume SizeTFitsU64 : fits_u64

[@@pulse_unfold]
unfold
let _true_ = true

[@@pulse_unfold]
unfold
let _false_ = false

let maybe (b:bool) (p:slprop) = if b then p else emp

ghost
fn intro_maybe (p:slprop)
requires p
ensures maybe _true_ p
{
  fold (maybe _true_ p)
}

ghost
fn intro_maybe_false (p:slprop)
requires emp
ensures maybe _false_ p
{
  fold (maybe _false_ p)
}