module Pulse.Lib.C.Sizeof

open FStar.SizeT

/// Reified C types used as arguments to opaque [c_sizeof] / [c_alignof].
/// These values do not commit to any specific platform layout — they
/// only identify the C type whose size or alignment is being asked for.
noeq type c_type =
  | C_Void
  | C_Bool
  | C_SizeT
  | C_PtrdiffT
  | C_Int : signed:bool -> width:nat -> c_type
  | C_Pointer : c_type -> c_type
  | C_Array : c_type -> nat -> c_type
  | C_Named : string -> c_type

/// Opaque size of a C type, in bytes. We commit to no specific value.
val c_sizeof : c_type -> t

/// Opaque alignment of a C type, in bytes. We commit to no specific value.
val c_alignof : c_type -> t

/// Sizes and alignments are always strictly positive on any conforming C
/// implementation.
val c_sizeof_pos (ty: c_type)
  : Lemma (v (c_sizeof ty) > 0)
    [SMTPat (v (c_sizeof ty))]

val c_alignof_pos (ty: c_type)
  : Lemma (v (c_alignof ty) > 0)
    [SMTPat (v (c_alignof ty))]

/// Array-type size decomposition: sizeof(T[n]) == n * sizeof(T).
val c_sizeof_array (ty: c_type) (n: nat)
  : Lemma (fits (n * v (c_sizeof ty)) /\
           v (c_sizeof (C_Array ty n)) == n * v (c_sizeof ty))
    [SMTPat (c_sizeof (C_Array ty n))]

/// Sign of an integer type does not affect its size (C standard).
val c_sizeof_int_sign (s1 s2: bool) (w: nat)
  : Lemma (c_sizeof (C_Int s1 w) == c_sizeof (C_Int s2 w))

/// For fixed-width integer types, the size in bytes is the width in bits
/// divided by the bits-per-byte (8) — i.e. `sizeof(intN_t) == N/8`. This
/// holds on any conforming C implementation where `CHAR_BIT == 8`.
val c_sizeof_int_width (s: bool) (w: nat)
  : Lemma (requires (w % 8 == 0))
          (ensures (v (c_sizeof (C_Int s w)) == w / 8))
    [SMTPat (c_sizeof (C_Int s w))]
