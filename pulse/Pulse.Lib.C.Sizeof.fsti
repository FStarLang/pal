module Pulse.Lib.C.Sizeof

open FStar.SizeT

/// Opaque byte-size of an arbitrary F* type, intended to be used as the
/// translation of `sizeof(T)` from C. The function commits to no
/// particular value — only that whatever it returns is non-negative.
val c_sizeof (a: Type u#a) : t

/// Opaque alignment-in-bytes of an arbitrary F* type, intended to be used
/// as the translation of `_Alignof(T)` from C.
val c_alignof (a: Type u#a) : t

/// Phantom representation of the C array type `a[n]`, used only as the type
/// argument to `c_sizeof` when translating `sizeof(a[n])`. It carries the
/// length `n` so the size of an array can be related to its element size.
val c_array (a: Type u#a) (n: nat) : Type u#a

/// Sizes are non-negative. Strict positivity does not hold for every type: a
/// zero-length array `a[0]` has size 0 (see `c_sizeof_array`).
val c_sizeof_nonneg (a: Type u#a)
  : Lemma (v (c_sizeof a) >= 0)
    [SMTPat (v (c_sizeof a))]

/// The size of the array type `a[n]` is the element size times the length.
/// This is an idealized model axiom: like `Pulse.Lib.C.Array.alloc`, it makes
/// no attempt to rule out `size_t` overflow for large `n`.
val c_sizeof_array (a: Type u#a) (n: nat)
  : Lemma (v (c_sizeof (c_array a n)) == v (c_sizeof a) * n)
    [SMTPat (v (c_sizeof (c_array a n)))]

/// Alignments are strictly positive on any conforming C implementation.
val c_alignof_pos (a: Type u#a)
  : Lemma (v (c_alignof a) > 0)
    [SMTPat (v (c_alignof a))]
