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

val c_sizeof_int16_pos (a: Type0 { a == FStar.Int16.t })
  : Lemma (v (c_sizeof a) > 0)
    [SMTPat (v (c_sizeof a))]

val c_sizeof_uint16_pos (a: Type0 { a == FStar.UInt16.t })
  : Lemma (v (c_sizeof a) > 0)
    [SMTPat (v (c_sizeof a))]

val c_sizeof_int32_pos (a: Type0 { a == FStar.Int32.t })
  : Lemma (v (c_sizeof a) > 0)
    [SMTPat (v (c_sizeof a))]

val c_sizeof_uint32_pos (a: Type0 { a == FStar.UInt32.t })
  : Lemma (v (c_sizeof a) > 0)
    [SMTPat (v (c_sizeof a))]

val c_sizeof_int64_pos (a: Type0 { a == FStar.Int64.t })
  : Lemma (v (c_sizeof a) > 0)
    [SMTPat (v (c_sizeof a))]

val c_sizeof_uint64_pos (a: Type0 { a == FStar.UInt64.t })
  : Lemma (v (c_sizeof a) > 0)
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
