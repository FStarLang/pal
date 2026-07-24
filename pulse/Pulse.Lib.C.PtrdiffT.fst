module Pulse.Lib.C.PtrdiffT

/// ptrdiff_t: signed integer type for pointer differences.
/// Modeled as Int64.t for 64-bit targets.

module I64 = FStar.Int64

let t = I64.t
let v (x: t) : int = I64.v x

/// Whether an integer is representable in `ptrdiff_t`. Used to state the
/// definedness precondition of pointer subtraction (C11 6.5.6p9).
let fits (x: int) : prop = I64.fits x

let zero : t = 0L
let one : t = 1L

let add (x y: t { I64.fits (I64.v x + I64.v y) }) : t = I64.add x y
let sub (x y: t { I64.fits (I64.v x - I64.v y) }) : t = I64.sub x y
let mul (x y: t { I64.fits (I64.v x * I64.v y) }) : t = I64.mul x y
let div (x y: t { I64.v y <> 0 /\ I64.fits (I64.v x / I64.v y) }) : t = I64.div x y
let rem (x y: t { I64.v y <> 0 /\ I64.fits (I64.v x / I64.v y) }) : t = I64.rem x y

let lte (x y: t) : bool = I64.lte x y
let lt (x y: t) : bool = I64.lt x y
let gte (x y: t) : bool = I64.gte x y
let gt (x y: t) : bool = I64.gt x y

let of_int (x: int { I64.fits x }) : t = I64.int_to_t x
