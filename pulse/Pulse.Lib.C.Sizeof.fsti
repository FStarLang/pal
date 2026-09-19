module Pulse.Lib.C.Sizeof

open FStar.SizeT
module Arr = Pulse.Lib.C.Array
module CR = Pulse.Lib.C.CoreRef
module FP = Pulse.Lib.C.FuncPtr
module PD = Pulse.Lib.C.PtrdiffT
module R = Pulse.Lib.Reference

/// Opaque byte-size of an arbitrary F* type, intended to be used as the
/// translation of `sizeof(T)` from C. The function commits to no
/// particular value — only that whatever it returns is non-negative.
val c_sizeof (a: Type u#a) : t

/// Opaque alignment-in-bytes of an arbitrary F* type, intended to be used
/// as the translation of `_Alignof(T)` from C.
val c_alignof (a: Type u#a) : t

/// Sizes are non-negative. Strict positivity does not hold for every type: a
/// zero-length array `a[0]` has size 0 (see `c_sizeof_array`).
val c_sizeof_nonneg (a: Type u#a)
  : Lemma (v (c_sizeof a) >= 0)
    [SMTPat (v (c_sizeof a))]

/// Scalar C types and pointer representations always occupy storage.
val c_sizeof_bool_pos (a: Type0 { a == bool })
  : Lemma (v (c_sizeof a) > 0)
    [SMTPat (v (c_sizeof a))]

/// The character types are the one case where C fixes the value rather than
/// merely bounding it: a byte is defined as the storage `char` occupies, so
/// `sizeof(char)`, `sizeof(signed char)` and `sizeof(unsigned char)` are 1 by
/// definition (C17 6.5.3.4p4). `int8_t` and `uint8_t` are covered by the same
/// fact -- they are required to have exactly 8 bits and no padding, which a
/// type larger than one byte cannot satisfy on an implementation where they
/// exist at all.
///
/// Stating it matters, because `sizeof` of a char ARRAY is the commonest way C
/// writes a buffer's length. `c_sizeof_array` gives
/// `sizeof(char[n]) == sizeof(char) * n`, so without this the size of a
/// 16-byte name field is only known to be "some positive multiple of 16", and
/// an obligation as ordinary as `sizeof(r->name) <= r->name._length` cannot be
/// discharged.
val c_sizeof_int8_one (a: Type0 { a == FStar.Int8.t })
  : Lemma (v (c_sizeof a) == 1)
    [SMTPat (v (c_sizeof a))]

val c_sizeof_uint8_one (a: Type0 { a == FStar.UInt8.t })
  : Lemma (v (c_sizeof a) == 1)
    [SMTPat (v (c_sizeof a))]

/// The wider integer types have exact sizes too, for the same reason as
/// `int8_t`/`uint8_t` above but by way of the translation rather than by way of
/// C alone. The derivation has three steps, and it is worth writing down
/// because the conclusion is stronger than what C by itself guarantees for the
/// non-exact-width types.
///
/// 1. PAL maps a C integer type to `FStar.UIntN.t`/`FStar.IntN.t` **by its bit
///    width as the target reports it** -- `TargetIntWidths` in
///    `src/hauntedc.rs`, consumed by `get_uint_mod`/`get_int_mod` in
///    `src/pass/emit.rs`. The model it then gives that type is full N-bit
///    modular arithmetic over all N bits: `Pulse.Lib.C.UIntN.add_wrap` wraps
///    modulo 2^N and `Pulse.Lib.C.BitField.mask_uN` masks all N of them. So in
///    PAL's model the type has exactly N value bits and no padding bits. (C
///    permits padding bits in integer types other than the character types and
///    the exact-width types; a program translated by PAL is already being
///    verified against a model in which they do not exist.)
///
/// 2. C17 6.2.6.1p4: an object of type T occupies `sizeof(T)` bytes of
///    CHAR_BIT bits each, and its object representation is exactly those bits.
///    With no padding bits, `sizeof(T) * CHAR_BIT == N`.
///
/// 3. `CHAR_BIT == 8`. PAL commits to this already by mapping `char` to
///    `FStar.UInt8.t`/`FStar.Int8.t` -- there is no `FStar.UInt9.t` to map it
///    to otherwise -- and `TargetIntWidths::default()` sets `char_width: 8`.
///
/// Hence `sizeof(T) == N / 8`.
///
/// **Residual assumption:** a target with `CHAR_BIT != 8`. PAL cannot translate
/// such a target correctly in the first place, so these axioms add no exposure
/// that the character-type mapping has not already taken on.
///
/// **Why bother.** `sizeof(x)` appears in C mostly inside an arithmetic
/// expression -- `sizeof(bmap) * 8 / bits_per_entry` to count the entries of a
/// bitmap, `sizeof(buf) / sizeof(buf[0])` to count an array's elements -- and
/// with only `sizeof > 0` known, the *multiplication* cannot be shown to fit in
/// `size_t`, so an ordinary bounds assertion fails on an obligation that has
/// nothing to do with bounds. These replace the `_pos` lemmas they supersede
/// rather than sitting alongside them: an `SMTPat` is paid by every query in
/// every PAL program, and two facts where one will do is a cost with no
/// benefit.

val c_sizeof_int16_two (a: Type0 { a == FStar.Int16.t })
  : Lemma (v (c_sizeof a) == 2)
    [SMTPat (v (c_sizeof a))]

val c_sizeof_uint16_two (a: Type0 { a == FStar.UInt16.t })
  : Lemma (v (c_sizeof a) == 2)
    [SMTPat (v (c_sizeof a))]

val c_sizeof_int32_four (a: Type0 { a == FStar.Int32.t })
  : Lemma (v (c_sizeof a) == 4)
    [SMTPat (v (c_sizeof a))]

val c_sizeof_uint32_four (a: Type0 { a == FStar.UInt32.t })
  : Lemma (v (c_sizeof a) == 4)
    [SMTPat (v (c_sizeof a))]

val c_sizeof_int64_eight (a: Type0 { a == FStar.Int64.t })
  : Lemma (v (c_sizeof a) == 8)
    [SMTPat (v (c_sizeof a))]

val c_sizeof_uint64_eight (a: Type0 { a == FStar.UInt64.t })
  : Lemma (v (c_sizeof a) == 8)
    [SMTPat (v (c_sizeof a))]

val c_sizeof_float32_pos (a: Type0 { a == FStar.Float32.t })
  : Lemma (v (c_sizeof a) > 0)
    [SMTPat (v (c_sizeof a))]

val c_sizeof_float64_pos (a: Type0 { a == FStar.Float64.t })
  : Lemma (v (c_sizeof a) > 0)
    [SMTPat (v (c_sizeof a))]

val c_sizeof_size_t_pos (a: Type0 { a == FStar.SizeT.t })
  : Lemma (v (c_sizeof a) > 0)
    [SMTPat (v (c_sizeof a))]

val c_sizeof_ptrdiff_t_pos (a: Type0 { a == PD.t })
  : Lemma (v (c_sizeof a) > 0)
    [SMTPat (v (c_sizeof a))]

val c_sizeof_ref_pos (a: Type u#a)
  : Lemma (v (c_sizeof (R.ref a)) > 0)
    [SMTPat (v (c_sizeof (R.ref a)))]

val c_sizeof_array_ptr_pos (a: Type u#a)
  : Lemma (v (c_sizeof (Arr.array a)) > 0)
    [SMTPat (v (c_sizeof (Arr.array a)))]

val c_sizeof_core_ref_pos (a: Type0 { a == CR.core_ref })
  : Lemma (v (c_sizeof a) > 0)
    [SMTPat (v (c_sizeof a))]

val c_sizeof_func_ptr_pos (a b: Type0)
  : Lemma (v (c_sizeof (FP.func_ptr a b)) > 0)
    [SMTPat (v (c_sizeof (FP.func_ptr a b)))]

/// The size of the C array type `a[n]` (modelled by `full_array_lspec a n`, the
/// same length-indexed array type used everywhere else) is the element size
/// times the length. This is an idealized model axiom: like
/// `Pulse.Lib.C.Array.alloc`, it makes no attempt to rule out `size_t` overflow
/// for large `n`.
val c_sizeof_array (a: Type u#a) (n: nat)
  : Lemma (v (c_sizeof (Arr.full_array_lspec a n)) == v (c_sizeof a) * n)
    [SMTPat (v (c_sizeof (Arr.full_array_lspec a n)))]

/// Alignments are strictly positive on any conforming C implementation.
val c_alignof_pos (a: Type u#a)
  : Lemma (v (c_alignof a) > 0)
    [SMTPat (v (c_alignof a))]
