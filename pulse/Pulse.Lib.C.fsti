module Pulse.Lib.C
#lang-pulse
include Pulse.Lib.C.Inhabited
include FStar.SizeT // before Int32 to not shadow fits there
include Pulse.Lib.C.Int32
include Pulse.Lib.C.Ref
include Pulse.Lib.C.Array
include Pulse.Class.PtsTo
include FStar.Int.Cast
include Pulse.Lib.C.Casts
include Pulse.Lib.C.UnaryOps
include Pulse.Lib.C.Sizeof
include Pulse.Lib.WithPure
open Pulse.Lib.Core
let _Bool = bool

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