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

val c_sizeof_int8_pos (a: Type0 { a == FStar.Int8.t })
  : Lemma (v (c_sizeof a) > 0)
    [SMTPat (v (c_sizeof a))]

val c_sizeof_uint8_pos (a: Type0 { a == FStar.UInt8.t })
  : Lemma (v (c_sizeof a) > 0)
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
