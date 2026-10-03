#include "pal.h"
#include <stdint.h>

/*
 * Where a bit-field lives in its storage unit is the ABI's decision, and the
 * two byte orders decide it differently: on a little-endian target the first
 * bit-field takes the unit's least significant bits, on a big-endian one its
 * most significant. PAL takes the allocation from clang and has to turn it
 * into a position in the unit's value, from the right end.
 *
 * This file is translated twice, for mips64 (`bitfield_layout_be`) and for
 * mips64el (`bitfield_layout_le`). Each function is handed the bytes the
 * compiler puts in memory for known field values, and has to read those
 * values back out through the bit-fields. The bytes are what
 *
 *     struct s1 g1 = { 1, 2, 0x345, 0x678 };
 *     struct s2 g2 = { 5, 0x1abcd, 0xfedcba98765 };
 *     struct s3 g3 = { 1, 0x2a, 0x1b3 };
 *     struct s4 g4 = { 0xee, 5, 0x13 };
 *
 * compiles to. `readelf -x .data` on the object from
 * `clang --target=mips64-unknown-linux-gnuabi64 -c` shows
 *
 *     12345678 00000000 babcdfed cba98765 d5b3 eeb3
 *
 * (`g2` is aligned to 8), and with mips64el
 *
 *     21458367 00000000 6d5e5d76 98badcfe d5d9 ee9d
 *
 * GCC agrees. The bytes are chosen by the preprocessor's own
 * `__BYTE_ORDER__`, so a position PAL got wrong for either order would read
 * something else and not verify.
 *
 * The units are 32, 64, 16 and 8 bits wide. The first three need the byte
 * order as well as the allocation order: their bytes become the unit's value
 * only through `TargetFacts`. `struct s4` has a one-byte unit after an
 * ordinary member, so there is no byte order to speak of, and only the
 * allocation order is at stake.
 *
 * `palow-only`: the old model has no bytes to read the fields out of.
 */

_include_pulse(Bitfield_layout_facts,
  module E = Pulse.Lib.C.Palow.Encoding
  module T = Pulse.Lib.C.Palow.Target
  open Union_s1_bytes
  open Union_s2_bytes
  open Union_s3_bytes
  open Union_s4_bytes

  (* The `n` bytes of `x` in the order the target stores them, whichever
     that is. *)
  let bytes_of (n: pos) (x: nat) : (s: Seq.seq UInt8.t { Seq.length s == n }) =
    Seq.init n (fun (i: nat { i < n }) ->
      UInt8.uint_to_t ((x / pow2 (8 * E.significance T.byte_order n i)) % 256))

  (* Bytes that are, one at a time, the bytes of `x` in the order of the
     target are the encoding of `x`. This holds on every target, so nothing
     here asks which. *)
  let bytes_as_value (n: pos) (x: nat) (b: bytes)
    : Lemma (requires array_repr uint8_t_repr 1 (bytes_of n x) b)
            (ensures  b == E.encode T.byte_order n None x)
    = let aux (i: nat { i < n })
        : Lemma (get b i == get (E.encode T.byte_order n None x) i)
        = assert_norm (pow2 0 == 1);
          assert uint8_t_repr (Seq.index (bytes_of n x) i) (elem_bytes 1 b i);
          Seq.lemma_index_slice b i (i + 1) 0
      in
      Classical.forall_intro aux;
      bytes_ext b (E.encode T.byte_order n None x)

  (* A union holding the bytes of `x` holds a struct whose unit is `x`. *)
  ghost fn s1_c_as_s (u: ptr) (x: UInt32.t) (#p: perm)
                    (#s: (s: Seq.seq UInt8.t { Seq.length s == 4 }))
    requires union_s1_bytes_pts_to u p (Union_s1_bytes_c s)
    requires pure (s == bytes_of 4 (UInt32.v x))
    ensures  union_s1_bytes_pts_to u p (Union_s1_bytes_s ({ Struct_s1.fld_bits0 = x }))
  {
    unfold union_s1_bytes_pts_to u p (Union_s1_bytes_c s);
    with b. assert mem_pts_to u p b;
    bytes_as_value 4 (UInt32.v x) (slice b 0 4);
    Seq.slice_slice b 0 4 0 4;
    fold union_s1_bytes_pts_to u p (Union_s1_bytes_s ({ Struct_s1.fld_bits0 = x }));
  }

  ghost fn s2_c_as_s (u: ptr) (x: UInt64.t) (#p: perm)
                    (#s: (s: Seq.seq UInt8.t { Seq.length s == 8 }))
    requires union_s2_bytes_pts_to u p (Union_s2_bytes_c s)
    requires pure (s == bytes_of 8 (UInt64.v x))
    ensures  union_s2_bytes_pts_to u p (Union_s2_bytes_s ({ Struct_s2.fld_bits0 = x }))
  {
    unfold union_s2_bytes_pts_to u p (Union_s2_bytes_c s);
    with b. assert mem_pts_to u p b;
    bytes_as_value 8 (UInt64.v x) (slice b 0 8);
    Seq.slice_slice b 0 8 0 8;
    fold union_s2_bytes_pts_to u p (Union_s2_bytes_s ({ Struct_s2.fld_bits0 = x }));
  }

  ghost fn s3_c_as_s (u: ptr) (x: UInt16.t) (#p: perm)
                    (#s: (s: Seq.seq UInt8.t { Seq.length s == 2 }))
    requires union_s3_bytes_pts_to u p (Union_s3_bytes_c s)
    requires pure (s == bytes_of 2 (UInt16.v x))
    ensures  union_s3_bytes_pts_to u p (Union_s3_bytes_s ({ Struct_s3.fld_bits0 = x }))
  {
    unfold union_s3_bytes_pts_to u p (Union_s3_bytes_c s);
    with b. assert mem_pts_to u p b;
    bytes_as_value 2 (UInt16.v x) (slice b 0 2);
    Seq.slice_slice b 0 2 0 2;
    fold union_s3_bytes_pts_to u p (Union_s3_bytes_s ({ Struct_s3.fld_bits0 = x }));
  }

  (* Byte sequences written the way `readelf` prints them. *)
  let img2 (b0 b1: UInt8.t) : (s: Seq.seq UInt8.t { Seq.length s == 2 }) =
    Seq.init 2 (fun (i: nat { i < 2 }) -> if i = 0 then b0 else b1)

  let img4 (b0 b1 b2 b3: UInt8.t) : (s: Seq.seq UInt8.t { Seq.length s == 4 }) =
    Seq.init 4 (fun (i: nat { i < 4 }) ->
      if i = 0 then b0 else if i = 1 then b1 else if i = 2 then b2 else b3)

  let img8 (b0 b1 b2 b3 b4 b5 b6 b7: UInt8.t) : (s: Seq.seq UInt8.t { Seq.length s == 8 }) =
    Seq.init 8 (fun (i: nat { i < 8 }) ->
      if i = 0 then b0 else if i = 1 then b1 else if i = 2 then b2 else if i = 3 then b3
      else if i = 4 then b4 else if i = 5 then b5 else if i = 6 then b6 else b7)

  (* A union holding two bytes holds a `struct s4` made of them. One byte has
     no order, so this too holds on every target. *)
  ghost fn s4_c_as_s (u: ptr) (#p: perm) (#x0 #x1: UInt8.t)
    requires union_s4_bytes_pts_to u p (Union_s4_bytes_c (img2 x0 x1))
    ensures  union_s4_bytes_pts_to u p
               (Union_s4_bytes_s ({ Struct_s4.fld_x = x0; Struct_s4.fld_bits1 = x1 }))
  {
    unfold union_s4_bytes_pts_to u p (Union_s4_bytes_c (img2 x0 x1));
    with b. assert mem_pts_to u p b;
    assert pure (uint8_t_repr x0 (elem_bytes 1 (slice b 0 2) 0));
    assert pure (uint8_t_repr x1 (elem_bytes 1 (slice b 0 2) 1));
    Seq.slice_slice b 0 2 0 1;
    Seq.slice_slice b 0 2 1 2;
    fold union_s4_bytes_pts_to u p
      (Union_s4_bytes_s ({ Struct_s4.fld_x = x0; Struct_s4.fld_bits1 = x1 }));
  }

  (* The powers of two the bit-field positions and widths of either order
     need, so that reading a field out of a known unit is arithmetic on
     numerals. *)
  let pow2_facts () : Lemma (pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 3 == 8 /\ pow2 4 == 16
                             /\ pow2 5 == 32 /\ pow2 6 == 64 /\ pow2 7 == 128
                             /\ pow2 8 == 256 /\ pow2 9 == 512 /\ pow2 12 == 4096
                             /\ pow2 15 == 32768 /\ pow2 17 == 131072
                             /\ pow2 20 == 1048576 /\ pow2 24 == 16777216
                             /\ pow2 28 == 268435456 /\ pow2 44 == 17592186044416
                             /\ pow2 61 == 2305843009213693952)
    = assert_norm (pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 3 == 8 /\ pow2 4 == 16
                   /\ pow2 5 == 32 /\ pow2 6 == 64 /\ pow2 7 == 128
                   /\ pow2 8 == 256 /\ pow2 9 == 512 /\ pow2 12 == 4096
                   /\ pow2 15 == 32768 /\ pow2 17 == 131072
                   /\ pow2 20 == 1048576 /\ pow2 24 == 16777216
                   /\ pow2 28 == 268435456 /\ pow2 44 == 17592186044416
                   /\ pow2 61 == 2305843009213693952)
)

/* What the compiler puts in memory, per order, and the value of each unit.
 * That the bytes are the unit is proved below, from `TargetFacts`. */
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
_include_pulse(Bitfield_layout_image,
  open Bitfield_layout_facts

  let s1_image = img4 0x12uy 0x34uy 0x56uy 0x78uy
  let s1_unit : UInt32.t = 0x12345678ul

  let s2_image = img8 0xbauy 0xbcuy 0xdfuy 0xeduy 0xcbuy 0xa9uy 0x87uy 0x65uy
  let s2_unit : UInt64.t = 0xbabcdfedcba98765uL

  let s3_image = img2 0xd5uy 0xb3uy
  let s3_unit : UInt16.t = 0xd5b3us

  (* byte 1 of `g4`; byte 0 is `x` *)
  let s4_bits : UInt8.t = 0xb3uy
)
#else
_include_pulse(Bitfield_layout_image,
  open Bitfield_layout_facts

  let s1_image = img4 0x21uy 0x45uy 0x83uy 0x67uy
  let s1_unit : UInt32.t = 0x67834521ul

  let s2_image = img8 0x6duy 0x5euy 0x5duy 0x76uy 0x98uy 0xbauy 0xdcuy 0xfeuy
  let s2_unit : UInt64.t = 0xfedcba98765d5e6duL

  let s3_image = img2 0xd5uy 0xd9uy
  let s3_unit : UInt16.t = 0xd9d5us

  (* byte 1 of `g4`; byte 0 is `x` *)
  let s4_bits : UInt8.t = 0x9duy
)
#endif

/* The bytes are the unit's bytes in the order of the target. Proved the same
 * way for both orders, from what `TargetFacts` says the order is. */
_include_pulse(Bitfield_layout_unit,
  module TF = Pulse.Lib.C.Palow.TargetFacts
  open Bitfield_layout_facts
  open Bitfield_layout_image

  let s1_image_is () : Lemma (s1_image == bytes_of 4 (UInt32.v s1_unit))
    = TF.byte_order_is ();
      let aux (i: nat { i < 4 })
        : Lemma (Seq.index s1_image i == Seq.index (bytes_of 4 (UInt32.v s1_unit)) i)
        = assert_norm (pow2 0 == 1 /\ pow2 8 == 256 /\ pow2 16 == 65536 /\ pow2 24 == 16777216);
          if i = 0 then () else if i = 1 then () else if i = 2 then () else ()
      in
      Classical.forall_intro aux;
      Seq.lemma_eq_intro s1_image (bytes_of 4 (UInt32.v s1_unit))

  let s2_image_is () : Lemma (s2_image == bytes_of 8 (UInt64.v s2_unit))
    = TF.byte_order_is ();
      let aux (i: nat { i < 8 })
        : Lemma (Seq.index s2_image i == Seq.index (bytes_of 8 (UInt64.v s2_unit)) i)
        = assert_norm (pow2 0 == 1 /\ pow2 8 == 256 /\ pow2 16 == 65536 /\ pow2 24 == 16777216
                       /\ pow2 32 == 4294967296 /\ pow2 40 == 1099511627776
                       /\ pow2 48 == 281474976710656 /\ pow2 56 == 72057594037927936);
          if i = 0 then () else if i = 1 then () else if i = 2 then () else if i = 3 then ()
          else if i = 4 then () else if i = 5 then () else if i = 6 then () else ()
      in
      Classical.forall_intro aux;
      Seq.lemma_eq_intro s2_image (bytes_of 8 (UInt64.v s2_unit))

  let s3_image_is () : Lemma (s3_image == bytes_of 2 (UInt16.v s3_unit))
    = TF.byte_order_is ();
      let aux (i: nat { i < 2 })
        : Lemma (Seq.index s3_image i == Seq.index (bytes_of 2 (UInt16.v s3_unit)) i)
        = assert_norm (pow2 0 == 1 /\ pow2 8 == 256);
          if i = 0 then () else ()
      in
      Classical.forall_intro aux;
      Seq.lemma_eq_intro s3_image (bytes_of 2 (UInt16.v s3_unit))
)

struct s1 {
  uint32_t a : 4, b : 4, c : 12, d : 12;
};

union s1_bytes {
  struct s1 s;
  uint8_t c[4];
};

struct s2 {
  uint64_t a : 3, b : 17, c : 44;
};

union s2_bytes {
  struct s2 s;
  uint8_t c[8];
};

struct s3 {
  uint16_t a : 1, b : 6, c : 9;
};

union s3_bytes {
  struct s3 s;
  uint8_t c[2];
};

struct s4 {
  uint8_t x;
  uint8_t a : 3, b : 5;
};

union s4_bytes {
  struct s4 s;
  uint8_t c[2];
};

/* Every field of `g1`, read out of the bytes the compiler lays out for it. */
_requires(_inline_pulse(union_s1_bytes_pts_to $(u) 1.0R
                          (Union_s1_bytes_c Bitfield_layout_image.s1_image)))
_ensures(_inline_pulse(union_s1_bytes_pts_to $(u) 1.0R
                         (Union_s1_bytes_s ({ Struct_s1.fld_bits0 = Bitfield_layout_image.s1_unit }))))
_ensures(return == 0x345)
uint32_t s1_fields(_plain union s1_bytes *u)
{
  _ghost_stmt(Bitfield_layout_unit.s1_image_is ());
  _ghost_stmt(Bitfield_layout_facts.s1_c_as_s $(u) Bitfield_layout_image.s1_unit);
  _ghost_stmt(Bitfield_layout_facts.pow2_facts ());
  uint32_t a = u->s.a;
  uint32_t b = u->s.b;
  uint32_t c = u->s.c;
  uint32_t d = u->s.d;
  _assert(a == 1);
  _assert(b == 2);
  _assert(c == 0x345);
  _assert(d == 0x678);
  return c;
}

/* Every field of `g2`, whose 44-bit field reaches across both halves of
 * its 64-bit unit. */
_requires(_inline_pulse(union_s2_bytes_pts_to $(u) 1.0R
                          (Union_s2_bytes_c Bitfield_layout_image.s2_image)))
_ensures(_inline_pulse(union_s2_bytes_pts_to $(u) 1.0R
                         (Union_s2_bytes_s ({ Struct_s2.fld_bits0 = Bitfield_layout_image.s2_unit }))))
_ensures(return == 0xfedcba98765)
uint64_t s2_fields(_plain union s2_bytes *u)
{
  _ghost_stmt(Bitfield_layout_unit.s2_image_is ());
  _ghost_stmt(Bitfield_layout_facts.s2_c_as_s $(u) Bitfield_layout_image.s2_unit);
  _ghost_stmt(Bitfield_layout_facts.pow2_facts ());
  uint64_t a = u->s.a;
  uint64_t b = u->s.b;
  uint64_t c = u->s.c;
  _assert(a == 5);
  _assert(b == 0x1abcd);
  _assert(c == 0xfedcba98765);
  return c;
}

/* Every field of `g3`, a 16-bit unit with fields of 1, 6 and 9 bits. */
_requires(_inline_pulse(union_s3_bytes_pts_to $(u) 1.0R
                          (Union_s3_bytes_c Bitfield_layout_image.s3_image)))
_ensures(_inline_pulse(union_s3_bytes_pts_to $(u) 1.0R
                         (Union_s3_bytes_s ({ Struct_s3.fld_bits0 = Bitfield_layout_image.s3_unit }))))
_ensures(return == 0x1b3)
uint16_t s3_fields(_plain union s3_bytes *u)
{
  _ghost_stmt(Bitfield_layout_unit.s3_image_is ());
  _ghost_stmt(Bitfield_layout_facts.s3_c_as_s $(u) Bitfield_layout_image.s3_unit);
  _ghost_stmt(Bitfield_layout_facts.pow2_facts ());
  uint16_t a = u->s.a;
  uint16_t b = u->s.b;
  uint16_t c = u->s.c;
  _assert(a == 1);
  _assert(b == 0x2a);
  _assert(c == 0x1b3);
  return c;
}

/* Every field of `g4`, whose one-byte unit follows an ordinary member. */
_requires(_inline_pulse(union_s4_bytes_pts_to $(u) 1.0R
                          (Union_s4_bytes_c (Bitfield_layout_facts.img2 0xeeuy Bitfield_layout_image.s4_bits))))
_ensures(_inline_pulse(union_s4_bytes_pts_to $(u) 1.0R
                         (Union_s4_bytes_s ({ Struct_s4.fld_x = 0xeeuy; Struct_s4.fld_bits1 = Bitfield_layout_image.s4_bits }))))
_ensures(return == 0x13)
uint8_t s4_fields(_plain union s4_bytes *u)
{
  _ghost_stmt(Bitfield_layout_facts.s4_c_as_s $(u));
  _ghost_stmt(Bitfield_layout_facts.pow2_facts ());
  uint8_t x = u->s.x;
  uint8_t a = u->s.a;
  uint8_t b = u->s.b;
  _assert(x == 0xee);
  _assert(a == 5);
  _assert(b == 0x13);
  return b;
}
