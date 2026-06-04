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

// Whether C assert() is enabled (i.e., NDEBUG is not defined).
// Opaque so the verifier must handle both cases, exposing any
// side effects in assert arguments that would change behavior
// when assertions are disabled.
val func_pal_c_assert_enabled (_:unit) : bool
