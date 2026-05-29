module Pulse.Lib.C.Sizeof

open FStar.SizeT

/// Opaque byte-size of an arbitrary F* type, intended to be used as the
/// translation of `sizeof(T)` from C. The function commits to no
/// particular value — only that whatever it returns is strictly positive.
val c_sizeof (a: Type u#a) : t

/// Opaque alignment-in-bytes of an arbitrary F* type, intended to be used
/// as the translation of `_Alignof(T)` from C.
val c_alignof (a: Type u#a) : t

/// Sizes are strictly positive on any conforming C implementation.
val c_sizeof_pos (a: Type u#a)
  : Lemma (v (c_sizeof a) > 0)
    [SMTPat (v (c_sizeof a))]

/// Alignments are strictly positive on any conforming C implementation.
val c_alignof_pos (a: Type u#a)
  : Lemma (v (c_alignof a) > 0)
    [SMTPat (v (c_alignof a))]
