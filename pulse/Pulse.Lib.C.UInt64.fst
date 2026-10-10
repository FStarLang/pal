module Pulse.Lib.C.UInt64

include FStar.UInt64
module U64 = FStar.UInt64

/// Wrapping (modular) arithmetic for unsigned C semantics: these are total
/// (no overflow precondition). The postcondition is exact when the result
/// fits and the wrapped value otherwise, so non-overflowing uses keep the
/// natural `v z == v x + v y` reasoning.
let add_wrap (x y: U64.t)
  : Pure U64.t
    (requires True)
    (ensures fun z ->
      if FStar.UInt.fits (U64.v x + U64.v y) U64.n
      then U64.v z == U64.v x + U64.v y
      else U64.v z == FStar.UInt.add_mod (U64.v x) (U64.v y))
  = U64.add_mod x y

let sub_wrap (x y: U64.t)
  : Pure U64.t
    (requires True)
    (ensures fun z ->
      if FStar.UInt.fits (U64.v x - U64.v y) U64.n
      then U64.v z == U64.v x - U64.v y
      else U64.v z == FStar.UInt.sub_mod (U64.v x) (U64.v y))
  = U64.sub_mod x y

let mul_wrap (x y: U64.t)
  : Pure U64.t
    (requires True)
    (ensures fun z ->
      if FStar.UInt.fits (U64.v x * U64.v y) U64.n
      then U64.v z == U64.v x * U64.v y
      else U64.v z == FStar.UInt.mul_mod (U64.v x) (U64.v y))
  = U64.mul_mod x y

/// Byte reversal, for `__builtin_bswap64`.
///
/// A definition, not an axiom: the builtin's meaning is entirely captured by
/// the shifts and masks below, so nothing new is assumed and the result can be
/// reasoned about to whatever depth a caller needs by unfolding it. Code
/// reaches this through big-endian hardware descriptors.
let bswap64 (x: U64.t) : U64.t =
  U64.logor
    (U64.logor
      (U64.logor
        (U64.shift_left (U64.logand x 0xFFuL) 56ul)
        (U64.shift_left (U64.logand (U64.shift_right x 8ul) 0xFFuL) 48ul))
      (U64.logor
        (U64.shift_left (U64.logand (U64.shift_right x 16ul) 0xFFuL) 40ul)
        (U64.shift_left (U64.logand (U64.shift_right x 24ul) 0xFFuL) 32ul)))
    (U64.logor
      (U64.logor
        (U64.shift_left (U64.logand (U64.shift_right x 32ul) 0xFFuL) 24ul)
        (U64.shift_left (U64.logand (U64.shift_right x 40ul) 0xFFuL) 16ul))
      (U64.logor
        (U64.shift_left (U64.logand (U64.shift_right x 48ul) 0xFFuL) 8ul)
        (U64.logand (U64.shift_right x 56ul) 0xFFuL)))

/// `bswap64` restated over `FStar.UInt.uint_t 64`, where the bit-vector tactic
/// applies; the machine operations are abstract, so it cannot see through them.
private
let bswap64_spec (x: FStar.UInt.uint_t 64) : FStar.UInt.uint_t 64 =
  let open FStar.UInt in
  logor #64
    (logor #64
      (logor #64
        (shift_left #64 (logand #64 x 0xFF) 56)
        (shift_left #64 (logand #64 (shift_right #64 x 8) 0xFF) 48))
      (logor #64
        (shift_left #64 (logand #64 (shift_right #64 x 16) 0xFF) 40)
        (shift_left #64 (logand #64 (shift_right #64 x 24) 0xFF) 32)))
    (logor #64
      (logor #64
        (shift_left #64 (logand #64 (shift_right #64 x 32) 0xFF) 24)
        (shift_left #64 (logand #64 (shift_right #64 x 40) 0xFF) 16))
      (logor #64
        (shift_left #64 (logand #64 (shift_right #64 x 48) 0xFF) 8)
        (logand #64 (shift_right #64 x 56) 0xFF)))

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
private
let bswap64_bridge (x: U64.t) : Lemma (U64.v (bswap64 x) == bswap64_spec (U64.v x)) = ()

private
let bswap64_spec_involutive (x: FStar.UInt.uint_t 64)
  : Lemma (bswap64_spec (bswap64_spec x) == x)
  = FStar.Tactics.V2.assert_by_tactic (bswap64_spec (bswap64_spec x) == x) (fun () ->
      FStar.Tactics.V2.norm [delta_only [`%bswap64_spec]];
      FStar.Tactics.BV.bv_tac ())

/// Byte reversal undoes itself. This is what code reading big-endian data
/// relies on, and it is not something SMT finds by unfolding.
let bswap64_involutive (x: U64.t)
  : Lemma (bswap64 (bswap64 x) == x) [SMTPat (bswap64 (bswap64 x))]
  = bswap64_bridge x;
    bswap64_bridge (bswap64 x);
    bswap64_spec_involutive (U64.v x);
    U64.v_inj (bswap64 (bswap64 x)) x
#pop-options
