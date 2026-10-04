module Pulse.Lib.C.Assumptions

open FStar.SizeT { fits, fits_u32, fits_u64, fits_u32_implies_fits }

// We assume size_t is at least 64 bits.
assume SizeTFitsU64 : fits_u64
assume SizeTFitsU32 : fits_u32

// Consequence of SizeTFitsU32: every non-negative value below 2^32 fits in size_t.
// Exposed with an SMTPat so the verifier can discharge size_t-fits goals automatically.
let sizet_fits_u32_pat (x:int)
  : Lemma
    (requires 0 <= x /\ x < FStar.UInt.max_int 32)
    (ensures fits x)
    [SMTPat (fits x)]
  = fits_u32_implies_fits x

let sizet_fits_u32_of_size_pat (x:int)
  : Lemma
    (requires 0 <= x /\ UInt.size x 32)
    (ensures SizeT.fits x)
    [SMTPat (SizeT.fits x)]
  = fits_u32_implies_fits x

// Consequence of SizeTFitsU64: every non-negative value below 2^64 fits in
// size_t, which is what makes converting a uint64_t back to size_t total.
let sizet_fits_u64_pat (x:int)
  : Lemma
    (requires 0 <= x /\ x < pow2 64)
    (ensures fits x)
    [SMTPat (fits x)]
  = FStar.SizeT.fits_u64_implies_fits x

// We also assume size_t is at most 64 bits, so it is exactly uint64_t. FStar.SizeT keeps
// the width abstract, but C's bitwise operators on size_t (`~x` above all)
// depend on it; Pulse.Lib.C.SizeTBits defines them through uint64_t using this.
// Consistent with FStar.SizeT's model, whose values are uint64_t values.
val sizet_v_lt_pow2_64 (x: FStar.SizeT.t)
  : Lemma (FStar.SizeT.v x < pow2 64)

// Whether C assert() is enabled (i.e., NDEBUG is not defined).
// Opaque so the verifier must handle both cases, exposing any
// side effects in assert arguments that would change behavior
// when assertions are disabled.
val func_pal_c_assert_enabled (_:unit) : bool
