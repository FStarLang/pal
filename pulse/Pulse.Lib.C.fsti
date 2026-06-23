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

type float32
type float64

val float32_zero : float32
val float64_zero : float64

val float32_of_string : string -> float32
val float64_of_string : string -> float64

val float32_neg : float32 -> float32
val float32_add : float32 -> float32 -> float32
val float32_sub : float32 -> float32 -> float32
val float32_mul : float32 -> float32 -> float32
val float32_div : float32 -> float32 -> float32
val float32_eq : float32 -> float32 -> bool
val float32_lt : float32 -> float32 -> bool
val float32_lte : float32 -> float32 -> bool
val float32_to_bool : float32 -> bool
val float32_of_bool : bool -> float32
val float32_to_int : float32 -> int
val float32_of_int : int -> float32

val float64_neg : float64 -> float64
val float64_add : float64 -> float64 -> float64
val float64_sub : float64 -> float64 -> float64
val float64_mul : float64 -> float64 -> float64
val float64_div : float64 -> float64 -> float64
val float64_eq : float64 -> float64 -> bool
val float64_lt : float64 -> float64 -> bool
val float64_lte : float64 -> float64 -> bool
val float64_to_bool : float64 -> bool
val float64_of_bool : bool -> float64
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