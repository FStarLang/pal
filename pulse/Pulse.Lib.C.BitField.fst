module Pulse.Lib.C.BitField

/// Truncation (masking) helpers for unsigned C bit-fields.
///
/// Assigning a value `v` to an `n`-bit unsigned bit-field stores the low `n`
/// bits of `v`, i.e. `v % pow2 n` (C unsigned modular truncation). PAL backs
/// each bit-field by a range-refined machine cell `(x:UW.t{UW.v x < pow2 n})`,
/// so the masked result must carry that bound as a refinement.
///
/// Each `mask_uW` truncates by modular arithmetic (`rem` by `pow2 n`), mirroring
/// how `add_wrap`/`sub_wrap`/`mul_wrap` model unsigned overflow via the modular
/// primitives. The `< pow2 n` bound then holds by "mod by a positive", needing
/// no bitwise reasoning; the exact value `UW.v r == UW.v v % pow2 n` comes
/// straight from the `rem` postcondition. The `n = W` case (field as wide as its
/// storage) is the identity, since the value already fits.

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Math = FStar.Math.Lemmas

let mask_u8 (n: nat { 0 < n /\ n <= 8 }) (v: U8.t)
  : (r:U8.t { U8.v r < pow2 n /\ U8.v r == U8.v v % pow2 n }) =
  if n = 8 then (Math.small_mod (U8.v v) (pow2 8); v)
  else (Math.pow2_lt_compat 8 n; U8.rem v (U8.uint_to_t (pow2 n)))

let mask_u16 (n: nat { 0 < n /\ n <= 16 }) (v: U16.t)
  : (r:U16.t { U16.v r < pow2 n /\ U16.v r == U16.v v % pow2 n }) =
  if n = 16 then (Math.small_mod (U16.v v) (pow2 16); v)
  else (Math.pow2_lt_compat 16 n; U16.rem v (U16.uint_to_t (pow2 n)))

let mask_u32 (n: nat { 0 < n /\ n <= 32 }) (v: U32.t)
  : (r:U32.t { U32.v r < pow2 n /\ U32.v r == U32.v v % pow2 n }) =
  if n = 32 then (Math.small_mod (U32.v v) (pow2 32); v)
  else (Math.pow2_lt_compat 32 n; U32.rem v (U32.uint_to_t (pow2 n)))

let mask_u64 (n: nat { 0 < n /\ n <= 64 }) (v: U64.t)
  : (r:U64.t { U64.v r < pow2 n /\ U64.v r == U64.v v % pow2 n }) =
  if n = 64 then (Math.small_mod (U64.v v) (pow2 64); v)
  else (Math.pow2_lt_compat 64 n; U64.rem v (U64.uint_to_t (pow2 n)))
