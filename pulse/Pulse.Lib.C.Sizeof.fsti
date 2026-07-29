module Pulse.Lib.C.Sizeof

open FStar.SizeT
module Arr = Pulse.Lib.C.Array

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
