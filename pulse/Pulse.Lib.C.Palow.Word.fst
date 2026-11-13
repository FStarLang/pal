module Pulse.Lib.C.Palow.Word
(* ---------------------------------------------------------------------------
   Word-at-a-time access to an array of bytes

   Reading `*w`, where `w` is a `size_t` pointer cast from a `char` pointer
   `s`, reads eight consecutive elements of a `char` array as one integer --
   the loop body of every fast `strlen`. C allows it for a `may_alias` word type when the bytes are there
   and the address is aligned for the word; what the read returns is whatever
   integer those bytes encode.

   Nothing here is assumed. The array is owned as `array_pts_to` of one-byte
   elements; the `W` elements at the walked pointer `q` are split out, which
   is `W` bytes of `mem_pts_to` at `q`, and those bytes -- initialised and
   provenance-free, since every element of the array holds a value -- are the
   encoding of exactly one `W`-byte integer (`encode_decode`). Given the
   alignment, that is the word type's own points-to, which the word type's
   ordinary read and write operate on. Putting it back is the same in
   reverse: whatever integer the word holds afterwards, its encoding is `W`
   one-byte elements again.

   What the caller learns is `word_bytes`: element `pos + j` is byte
   `byte_index W j` of the value, i.e. `(v / pow2 (8 * byte_index W j)) % 256`
   -- on a little-endian target, byte `j`. The element type enters only
   through `ev`, the byte an element is stored as (`bytelike`), so `char`
   arrays and `unsigned char` arrays are handled alike.

   The access requires `pos + W <= length`. The trusted over-read that drops
   it for an aligned word whose first byte is in bounds is in
   `Pulse.Lib.C.Palow.Overread`, separately, so that nothing reaches it by
   accident.
   --------------------------------------------------------------------------- *)
#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Encoding
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes
open Pulse.Lib.C.Palow.Machine
open Pulse.Lib.C.Palow.Array
open Pulse.Lib.C.Palow.Pun

module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I8 = FStar.Int8
module M = FStar.Math.Lemmas
module T = Pulse.Lib.C.Palow.Target

(* ---------------------------------------------------------------------------
   One-byte element types
   --------------------------------------------------------------------------- *)

(* An element type stored as one byte: `ev x` is that byte, and `ef` is the
   element a byte value reads back as. *)
[@@"opaque_to_smt"]
let bytelike (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t) : prop =
  (forall (x: t) (b: bytes). t_repr x b <==> b == encode 1 None (ev x)) /\
  (forall (x: t). ev x < 256) /\
  (forall (n: nat). n < 256 ==> ev (ef n) == n)

let uint8_t_byte (x: U8.t) : nat = U8.v x
let uint8_t_of_byte (n: nat) : U8.t = U8.uint_to_t (n % 256)

let int8_t_byte (x: I8.t) : nat = to_bits 8 (I8.v x)
let int8_t_of_byte (n: nat) : I8.t =
  assert_norm (pow2 8 == 256);
  I8.int_to_t (from_bits 8 (n % 256))

let reveal_bytelike (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
  : Lemma (bytelike t_repr ev ef <==>
           ((forall (x: t) (b: bytes). t_repr x b <==> b == encode 1 None (ev x)) /\
            (forall (x: t). ev x < 256) /\
            (forall (n: nat). n < 256 ==> ev (ef n) == n)))
  = reveal_opaque (`%bytelike) (bytelike t_repr ev ef)

let uint8_t_bytelike : squash (bytelike uint8_t_repr uint8_t_byte uint8_t_of_byte) =
  reveal_bytelike uint8_t_repr uint8_t_byte uint8_t_of_byte

let int8_t_bytelike : squash (bytelike int8_t_repr int8_t_byte int8_t_of_byte) =
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 7 == 128);
  let aux (n: nat) : Lemma (n < 256 ==> int8_t_byte (int8_t_of_byte n) == n) =
    if n < 256 then to_from_bits 8 n
  in
  FStar.Classical.forall_intro aux;
  reveal_bytelike int8_t_repr int8_t_byte int8_t_of_byte

(* ---------------------------------------------------------------------------
   The bytes of a word
   --------------------------------------------------------------------------- *)

(* Byte `j` of the value `x` in a `w`-byte representation. *)
[@@"opaque_to_smt"]
let word_byte (w: nat) (x: nat) (j: nat { j < w }) : (n: nat { n < 256 }) =
  (x / pow2 (8 * byte_index w j)) % 256

let reveal_word_byte (w: nat) (x: nat) (j: nat { j < w })
  : Lemma (word_byte w x j == (x / pow2 (8 * byte_index w j)) % 256)
  = reveal_opaque (`%word_byte) (word_byte w x j)

(* Those of elements `i .. i + w` of `xs` that exist are the bytes of the
   `w`-byte value `x` (an over-read word, see `Pulse.Lib.C.Palow.Overread`,
   says no more). Opaque: the quantifier would otherwise be instantiated at
   every array read of a function; it is used through the unrolling and
   `_at` lemmas below. *)
[@@"opaque_to_smt"]
let word_bytes_upto (#t: Type0) (ev: t -> nat) (xs: Seq.seq t) (i: nat) (w: nat) (x: nat) : prop =
  forall (j: nat). j < w /\ i + j < Seq.length xs ==> ev (Seq.index xs (i + j)) == word_byte w x j

let reveal_word_bytes_upto (#t: Type0) (ev: t -> nat) (xs: Seq.seq t) (i: nat) (w: nat) (x: nat)
  : Lemma (word_bytes_upto ev xs i w x <==>
           (forall (j: nat). j < w /\ i + j < Seq.length xs ==>
             ev (Seq.index xs (i + j)) == word_byte w x j))
  = reveal_opaque (`%word_bytes_upto) (word_bytes_upto ev xs i w x)

(* Elements `i .. i + w` of `xs` are the bytes of the `w`-byte value `x`. *)
let word_bytes (#t: Type0) (ev: t -> nat) (xs: Seq.seq t) (i: nat) (w: nat) (x: nat) : prop =
  i + w <= Seq.length xs /\ word_bytes_upto ev xs i w x

let reveal_word_bytes (#t: Type0) (ev: t -> nat) (xs: Seq.seq t) (i: nat) (w: nat) (x: nat)
  : Lemma (word_bytes ev xs i w x <==>
           (i + w <= Seq.length xs /\
            (forall (j: nat). j < w ==> ev (Seq.index xs (i + j)) == word_byte w x j)))
  = reveal_word_bytes_upto ev xs i w x

(* On the little-endian target the generated modules assume, byte `j` of a
   word is `x / 256^j % 256` with the power as a numeral -- the form a
   condition in the source divides by. Stated here once, because the solver
   gets there from `word_byte` only by unfolding `byte_index` and `pow2`. *)
let word_byte_le (w x: nat) (j: nat { j < w })
  : Lemma (requires T.little_endian == true)
          (ensures  word_byte w x j == x / pow2 (8 * j) % 256)
  = reveal_word_byte w x j

let word_byte_lits_2 (x: nat) (j: nat { j < 2 })
  : Lemma (requires T.little_endian == true)
          (ensures  word_byte 2 x j == (if j = 0 then x % 256 else x / 256 % 256))
          [SMTPat (word_byte 2 x j)]
  = assert (x / 1 == x);
    if j = 0 then (assert (j == 0); word_byte_le 2 x 0; assert_norm (pow2 (8 * 0) == 1); assert (word_byte 2 x j == x / 1 % 256))
    else (assert (j == 1); word_byte_le 2 x 1; assert_norm (pow2 (8 * 1) == 256); assert (word_byte 2 x j == x / 256 % 256))

let word_byte_lits_4 (x: nat) (j: nat { j < 4 })
  : Lemma (requires T.little_endian == true)
          (ensures  word_byte 4 x j == (if j = 0 then x % 256 else (if j = 1 then x / 256 % 256 else (if j = 2 then x / 65536 % 256 else x / 16777216 % 256))))
          [SMTPat (word_byte 4 x j)]
  = assert (x / 1 == x);
    if j = 0 then (assert (j == 0); word_byte_le 4 x 0; assert_norm (pow2 (8 * 0) == 1); assert (word_byte 4 x j == x / 1 % 256))
    else if j = 1 then (assert (j == 1); word_byte_le 4 x 1; assert_norm (pow2 (8 * 1) == 256); assert (word_byte 4 x j == x / 256 % 256))
    else if j = 2 then (assert (j == 2); word_byte_le 4 x 2; assert_norm (pow2 (8 * 2) == 65536); assert (word_byte 4 x j == x / 65536 % 256))
    else (assert (j == 3); word_byte_le 4 x 3; assert_norm (pow2 (8 * 3) == 16777216); assert (word_byte 4 x j == x / 16777216 % 256))

let word_byte_lits_8 (x: nat) (j: nat { j < 8 })
  : Lemma (requires T.little_endian == true)
          (ensures  word_byte 8 x j == (if j = 0 then x % 256 else (if j = 1 then x / 256 % 256 else (if j = 2 then x / 65536 % 256 else (if j = 3 then x / 16777216 % 256 else (if j = 4 then x / 4294967296 % 256 else (if j = 5 then x / 1099511627776 % 256 else (if j = 6 then x / 281474976710656 % 256 else x / 72057594037927936 % 256))))))))
          [SMTPat (word_byte 8 x j)]
  = assert (x / 1 == x);
    if j = 0 then (assert (j == 0); word_byte_le 8 x 0; assert_norm (pow2 (8 * 0) == 1); assert (word_byte 8 x j == x / 1 % 256))
    else if j = 1 then (assert (j == 1); word_byte_le 8 x 1; assert_norm (pow2 (8 * 1) == 256); assert (word_byte 8 x j == x / 256 % 256))
    else if j = 2 then (assert (j == 2); word_byte_le 8 x 2; assert_norm (pow2 (8 * 2) == 65536); assert (word_byte 8 x j == x / 65536 % 256))
    else if j = 3 then (assert (j == 3); word_byte_le 8 x 3; assert_norm (pow2 (8 * 3) == 16777216); assert (word_byte 8 x j == x / 16777216 % 256))
    else if j = 4 then (assert (j == 4); word_byte_le 8 x 4; assert_norm (pow2 (8 * 4) == 4294967296); assert (word_byte 8 x j == x / 4294967296 % 256))
    else if j = 5 then (assert (j == 5); word_byte_le 8 x 5; assert_norm (pow2 (8 * 5) == 1099511627776); assert (word_byte 8 x j == x / 1099511627776 % 256))
    else if j = 6 then (assert (j == 6); word_byte_le 8 x 6; assert_norm (pow2 (8 * 6) == 281474976710656); assert (word_byte 8 x j == x / 281474976710656 % 256))
    else (assert (j == 7); word_byte_le 8 x 7; assert_norm (pow2 (8 * 7) == 72057594037927936); assert (word_byte 8 x j == x / 72057594037927936 % 256))

(* The same, one conjunct per byte: what a proof about a particular byte of a
   word needs, without having to instantiate the quantifier at the right
   index. *)
let word_bytes_2 (#t: Type0) (ev: t -> nat) (xs: Seq.seq t) (i: nat) (x: nat)
  : Lemma (requires word_bytes ev xs i 2 x)
          (ensures  ev (Seq.index xs i) == word_byte 2 x 0 /\
                    ev (Seq.index xs (i + 1)) == word_byte 2 x 1)
          [SMTPat (word_bytes ev xs i 2 x)]
  = reveal_word_bytes ev xs i 2 x;
    assert (ev (Seq.index xs (i + 0)) == word_byte 2 x 0);
    assert (ev (Seq.index xs (i + 1)) == word_byte 2 x 1)

let word_bytes_4 (#t: Type0) (ev: t -> nat) (xs: Seq.seq t) (i: nat) (x: nat)
  : Lemma (requires word_bytes ev xs i 4 x)
          (ensures  ev (Seq.index xs i) == word_byte 4 x 0 /\
                    ev (Seq.index xs (i + 1)) == word_byte 4 x 1 /\
                    ev (Seq.index xs (i + 2)) == word_byte 4 x 2 /\
                    ev (Seq.index xs (i + 3)) == word_byte 4 x 3)
          [SMTPat (word_bytes ev xs i 4 x)]
  = reveal_word_bytes ev xs i 4 x;
    assert (ev (Seq.index xs (i + 0)) == word_byte 4 x 0);
    assert (ev (Seq.index xs (i + 1)) == word_byte 4 x 1);
    assert (ev (Seq.index xs (i + 2)) == word_byte 4 x 2);
    assert (ev (Seq.index xs (i + 3)) == word_byte 4 x 3)

let word_bytes_8 (#t: Type0) (ev: t -> nat) (xs: Seq.seq t) (i: nat) (x: nat)
  : Lemma (requires word_bytes ev xs i 8 x)
          (ensures  ev (Seq.index xs i) == word_byte 8 x 0 /\
                    ev (Seq.index xs (i + 1)) == word_byte 8 x 1 /\
                    ev (Seq.index xs (i + 2)) == word_byte 8 x 2 /\
                    ev (Seq.index xs (i + 3)) == word_byte 8 x 3 /\
                    ev (Seq.index xs (i + 4)) == word_byte 8 x 4 /\
                    ev (Seq.index xs (i + 5)) == word_byte 8 x 5 /\
                    ev (Seq.index xs (i + 6)) == word_byte 8 x 6 /\
                    ev (Seq.index xs (i + 7)) == word_byte 8 x 7)
          [SMTPat (word_bytes ev xs i 8 x)]
  = reveal_word_bytes ev xs i 8 x;
    assert (ev (Seq.index xs (i + 0)) == word_byte 8 x 0);
    assert (ev (Seq.index xs (i + 1)) == word_byte 8 x 1);
    assert (ev (Seq.index xs (i + 2)) == word_byte 8 x 2);
    assert (ev (Seq.index xs (i + 3)) == word_byte 8 x 3);
    assert (ev (Seq.index xs (i + 4)) == word_byte 8 x 4);
    assert (ev (Seq.index xs (i + 5)) == word_byte 8 x 5);
    assert (ev (Seq.index xs (i + 6)) == word_byte 8 x 6);
    assert (ev (Seq.index xs (i + 7)) == word_byte 8 x 7)

let word_bytes_upto_2 (#t: Type0) (ev: t -> nat) (xs: Seq.seq t) (i: nat) (x: nat)
  : Lemma (requires word_bytes_upto ev xs i 2 x)
          (ensures  (i + 0 < Seq.length xs ==> ev (Seq.index xs (i + 0)) == word_byte 2 x 0) /\
                    (i + 1 < Seq.length xs ==> ev (Seq.index xs (i + 1)) == word_byte 2 x 1))
          [SMTPat (word_bytes_upto ev xs i 2 x)]
  = reveal_word_bytes_upto ev xs i 2 x;
    assert (i + 0 < Seq.length xs ==> ev (Seq.index xs (i + 0)) == word_byte 2 x 0);
    assert (i + 1 < Seq.length xs ==> ev (Seq.index xs (i + 1)) == word_byte 2 x 1)

let word_bytes_upto_4 (#t: Type0) (ev: t -> nat) (xs: Seq.seq t) (i: nat) (x: nat)
  : Lemma (requires word_bytes_upto ev xs i 4 x)
          (ensures  (i + 0 < Seq.length xs ==> ev (Seq.index xs (i + 0)) == word_byte 4 x 0) /\
                    (i + 1 < Seq.length xs ==> ev (Seq.index xs (i + 1)) == word_byte 4 x 1) /\
                    (i + 2 < Seq.length xs ==> ev (Seq.index xs (i + 2)) == word_byte 4 x 2) /\
                    (i + 3 < Seq.length xs ==> ev (Seq.index xs (i + 3)) == word_byte 4 x 3))
          [SMTPat (word_bytes_upto ev xs i 4 x)]
  = reveal_word_bytes_upto ev xs i 4 x;
    assert (i + 0 < Seq.length xs ==> ev (Seq.index xs (i + 0)) == word_byte 4 x 0);
    assert (i + 1 < Seq.length xs ==> ev (Seq.index xs (i + 1)) == word_byte 4 x 1);
    assert (i + 2 < Seq.length xs ==> ev (Seq.index xs (i + 2)) == word_byte 4 x 2);
    assert (i + 3 < Seq.length xs ==> ev (Seq.index xs (i + 3)) == word_byte 4 x 3)

let word_bytes_upto_8 (#t: Type0) (ev: t -> nat) (xs: Seq.seq t) (i: nat) (x: nat)
  : Lemma (requires word_bytes_upto ev xs i 8 x)
          (ensures  (i + 0 < Seq.length xs ==> ev (Seq.index xs (i + 0)) == word_byte 8 x 0) /\
                    (i + 1 < Seq.length xs ==> ev (Seq.index xs (i + 1)) == word_byte 8 x 1) /\
                    (i + 2 < Seq.length xs ==> ev (Seq.index xs (i + 2)) == word_byte 8 x 2) /\
                    (i + 3 < Seq.length xs ==> ev (Seq.index xs (i + 3)) == word_byte 8 x 3) /\
                    (i + 4 < Seq.length xs ==> ev (Seq.index xs (i + 4)) == word_byte 8 x 4) /\
                    (i + 5 < Seq.length xs ==> ev (Seq.index xs (i + 5)) == word_byte 8 x 5) /\
                    (i + 6 < Seq.length xs ==> ev (Seq.index xs (i + 6)) == word_byte 8 x 6) /\
                    (i + 7 < Seq.length xs ==> ev (Seq.index xs (i + 7)) == word_byte 8 x 7))
          [SMTPat (word_bytes_upto ev xs i 8 x)]
  = reveal_word_bytes_upto ev xs i 8 x;
    assert (i + 0 < Seq.length xs ==> ev (Seq.index xs (i + 0)) == word_byte 8 x 0);
    assert (i + 1 < Seq.length xs ==> ev (Seq.index xs (i + 1)) == word_byte 8 x 1);
    assert (i + 2 < Seq.length xs ==> ev (Seq.index xs (i + 2)) == word_byte 8 x 2);
    assert (i + 3 < Seq.length xs ==> ev (Seq.index xs (i + 3)) == word_byte 8 x 3);
    assert (i + 4 < Seq.length xs ==> ev (Seq.index xs (i + 4)) == word_byte 8 x 4);
    assert (i + 5 < Seq.length xs ==> ev (Seq.index xs (i + 5)) == word_byte 8 x 5);
    assert (i + 6 < Seq.length xs ==> ev (Seq.index xs (i + 6)) == word_byte 8 x 6);
    assert (i + 7 < Seq.length xs ==> ev (Seq.index xs (i + 7)) == word_byte 8 x 7)

(* The array after the word at `i` has been overwritten with `x`. *)
let word_upd (#t: Type0) (ef: nat -> t) (xs: Seq.seq t) (i: nat) (w: nat) (x: nat) : Seq.seq t =
  Seq.init (Seq.length xs) (fun k ->
    if i <= k && k < i + w then ef (word_byte w x (k - i)) else Seq.index xs k)

let word_upd_length (#t: Type0) (ef: nat -> t) (xs: Seq.seq t) (i: nat) (w: nat) (x: nat)
  : Lemma (Seq.length (word_upd ef xs i w x) == Seq.length xs)
          [SMTPat (Seq.length (word_upd ef xs i w x))]
  = ()

let word_upd_index (#t: Type0) (ef: nat -> t) (xs: Seq.seq t) (i: nat) (w: nat) (x: nat) (k: nat)
  : Lemma (requires k < Seq.length xs)
          (ensures  Seq.index (word_upd ef xs i w x) k ==
                    (if i <= k && k < i + w then ef (word_byte w x (k - i)) else Seq.index xs k))
          [SMTPat (Seq.index (word_upd ef xs i w x) k)]
  = ()

let word_upd_bytes (#t: Type0) (ev: t -> nat) (ef: nat -> t) (xs: Seq.seq t) (i: nat) (w: nat) (x: nat)
  : Lemma (requires i + w <= Seq.length xs /\ (forall (n: nat). n < 256 ==> ev (ef n) == n))
          (ensures  word_bytes ev (word_upd ef xs i w x) i w x)
          [SMTPat (word_bytes ev (word_upd ef xs i w x) i w x)]
  = reveal_word_bytes ev (word_upd ef xs i w x) i w x

(* ---------------------------------------------------------------------------
   The pure core: `W` one-byte elements are the encoding of their word
   --------------------------------------------------------------------------- *)

let byte_at_inj (x y: nat)
  : Lemma (requires (byte_at None x 0).value == (byte_at None y 0).value /\ x < 256 /\ y < 256)
          (ensures  x == y)
  = assert_norm (pow2 0 == 1);
    M.small_mod x 256;
    M.small_mod y 256

let byte_at_word (x: nat) (k: nat)
  : Lemma (byte_at None x k == byte_at None ((x / pow2 (8 * k)) % 256) 0)
  = assert_norm (pow2 0 == 1);
    let r = (x / pow2 (8 * k)) % 256 in
    M.small_mod r 256;
    assert (r / pow2 0 == r)

let byte_index_one (_: unit) : Lemma (byte_index 1 0 == 0) = ()

let encode_one (v: nat)
  : Lemma (len (encode 1 None v) == 1 /\ get (encode 1 None v) 0 == byte_at None v 0)
  = encode_index 1 None v 0;
    byte_index_one ()

(* What `bytelike` says of a single element's byte. *)
let elem_byte (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
              (x: t) (c: bytes)
  : Lemma (requires bytelike t_repr ev ef /\ t_repr x c)
          (ensures  len c == 1 /\ get c 0 == byte_at None (ev x) 0 /\ ev x < 256)
  = reveal_bytelike t_repr ev ef;
    encode_one (ev x)

let elem_of_byte (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                 (x: t) (c: bytes)
  : Lemma (requires bytelike t_repr ev ef /\ len c == 1 /\ get c 0 == byte_at None (ev x) 0)
          (ensures  t_repr x c)
  = reveal_bytelike t_repr ev ef;
    encode_one (ev x);
    let e = encode 1 None (ev x) in
    let aux (i: nat { i < Seq.length c }) : Lemma (Seq.index c i == Seq.index e i) =
      assert (i == 0)
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro c e

let elem_bytes_get (b: bytes) (j: nat { j < len b })
  : Lemma (len (elem_bytes 1 b j) == 1 /\ get (elem_bytes 1 b j) 0 == get b j)
  = ()

(* The elements' bytes are plain, so the range is the encoding of a value,
   and that value's bytes are the elements. *)
let elems_word (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
               (mid: Seq.seq t) (b: bytes)
  : Lemma (requires bytelike t_repr ev ef /\ array_repr t_repr 1 mid b)
          (ensures  plain b /\ len b == Seq.length mid /\
                    bytes_nat b < pow2 (8 * len b) /\
                    b == encode (len b) None (bytes_nat b) /\
                    word_bytes ev mid 0 (len b) (bytes_nat b))
  = let n = len b in
    assert (n == Seq.length mid);
    let elem (j: nat { j < n })
      : Lemma (get b j == byte_at None (ev (Seq.index mid j)) 0 /\ ev (Seq.index mid j) < 256) =
      assert (t_repr (Seq.index mid j) (elem_bytes 1 b j));
      elem_bytes_get b j;
      elem_byte t_repr ev ef (Seq.index mid j) (elem_bytes 1 b j)
    in
    let aux (j: nat { j < n }) : Lemma (Some? (get b j).value /\ (get b j).prov == None) =
      elem j
    in
    FStar.Classical.forall_intro aux;
    assert (plain b);
    encode_decode b;
    let aux2 (j: nat { j < n }) : Lemma (ev (Seq.index mid (0 + j)) == word_byte n (bytes_nat b) j) =
      elem j;
      encode_index n None (bytes_nat b) j;
      byte_at_word (bytes_nat b) (byte_index n j);
      reveal_word_byte n (bytes_nat b) j;
      byte_at_inj (ev (Seq.index mid j)) (word_byte n (bytes_nat b) j)
    in
    FStar.Classical.forall_intro aux2;
    reveal_word_bytes ev mid 0 (len b) (bytes_nat b)

(* And back: elements that are the bytes of `x` are represented by its
   encoding. *)
let word_elems (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
               (mid: Seq.seq t) (x: nat)
  : Lemma (requires bytelike t_repr ev ef /\ word_bytes ev mid 0 (Seq.length mid) x)
          (ensures  array_repr t_repr 1 mid (encode (Seq.length mid) None x))
  = reveal_word_bytes ev mid 0 (Seq.length mid) x; reveal_bytelike t_repr ev ef;
    let n = Seq.length mid in
    let b = encode n None x in
    let aux (j: nat { j < Seq.length mid }) : Lemma (t_repr (Seq.index mid j) (elem_bytes 1 b j)) =
      let m = Seq.index mid j in
      assert (ev (Seq.index mid (0 + j)) == word_byte n x j);
      assert (ev m < 256);
      encode_index n None x j;
      byte_at_word x (byte_index n j);
      reveal_word_byte n x j;
      elem_bytes_get b j;
      elem_of_byte t_repr ev ef m (elem_bytes 1 b j)
    in
    FStar.Classical.forall_intro aux

let word_bytes_slice (#t: Type0) (ev: t -> nat) (xs: Seq.seq t) (i: nat) (w: nat) (x: nat)
  : Lemma (requires i + w <= Seq.length xs)
          (ensures  word_bytes ev (Seq.slice xs i (i + w)) 0 w x <==> word_bytes ev xs i w x)
  = let mid = Seq.slice xs i (i + w) in
    let aux (j: nat { j < w }) : Lemma (Seq.index mid (0 + j) == Seq.index xs (i + j)) = () in
    FStar.Classical.forall_intro aux;
    reveal_word_bytes ev mid 0 w x;
    reveal_word_bytes ev xs i w x

let join_off (#t: Type0) (n: SZ.t) (s: Seq.seq t)
  : Lemma (requires SZ.v n == Seq.length s) (ensures SZ.v n == 1 * Seq.length s)
  = ()

(* Putting a word back between the two slices around it. *)
let word_splice (#t: Type0) (xs ys: Seq.seq t) (i w: nat)
  : Lemma (requires i + w <= Seq.length xs /\ Seq.length ys == Seq.length xs /\
                    (forall (k: nat). k < Seq.length xs /\ (k < i \/ k >= i + w) ==>
                                      Seq.index ys k == Seq.index xs k))
          (ensures  Seq.append (Seq.slice xs 0 i)
                               (Seq.append (Seq.slice ys i (i + w))
                                           (Seq.slice xs (i + w) (Seq.length xs))) == ys)
  = let r = Seq.append (Seq.slice xs 0 i)
                       (Seq.append (Seq.slice ys i (i + w))
                                   (Seq.slice xs (i + w) (Seq.length xs))) in
    assert (Seq.length r == Seq.length ys);
    let aux (k: nat { k < Seq.length ys }) : Lemma (Seq.index r k == Seq.index ys k) =
      if k < i then () else if k < i + w then () else ()
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro r ys

let walk_here (a q: ptr) (n: nat) (i: SZ.t)
  : Lemma (requires walk_ok 1 a q /\ walk_idx 1 a q == SZ.v i /\ SZ.v i <= n /\
                    addr_of a + n < T.addr_limit)
          (ensures  a +! i == q)
  = addr_of_add_nowrap a i;
    ptr_ext (a +! i) q

(* ---------------------------------------------------------------------------
   Splitting the word's bytes out of the array, and putting them back
   --------------------------------------------------------------------------- *)

(* A position in a byte array is a byte offset; saying so keeps the solver
   off the division `walk_idx` is defined with. *)
let walk_idx_one (a q: ptr)
  : Lemma (requires walk_ok 1 a q)
          (ensures  walk_idx 1 a q == addr_of q - addr_of a /\ walk_idx 1 a q >= 0)
          [SMTPat (walk_idx 1 a q)]
  = ()

(* An offset that stays below `addr_limit` does not wrap. The solver would
   otherwise have to reduce modulo a limit it only knows as a `pow2`. *)
let addr_of_add_small (q: ptr) (n: SZ.t)
  : Lemma (requires addr_of q + SZ.v n < T.addr_limit)
          (ensures  addr_of (q +! n) == addr_of q + SZ.v n)
          [SMTPat (addr_of (q +! n))]
  = addr_of_add_nowrap q n

(* A step of a word pointer through a byte array: `w++` is `w +! W`. *)
let walk_step_one (a q: ptr) (n: SZ.t)
  : Lemma (requires walk_ok 1 a q /\ addr_of q + SZ.v n < T.addr_limit)
          (ensures  walk_ok 1 a (q +! n) /\ walk_idx 1 a (q +! n) == walk_idx 1 a q + SZ.v n /\
                    addr_of (q +! n) == addr_of q + SZ.v n)
          [SMTPatOr [[SMTPat (walk_ok 1 a (q +! n))]; [SMTPat (walk_idx 1 a (q +! n))]]]
  = addr_of_add_nowrap q n

let word_in (#t: Type0) (a q: ptr) (xs: Seq.seq t) (w: nat) : prop =
  walk_ok 1 a q /\ walk_idx 1 a q + w <= Seq.length xs

ghost fn array_bytes_focus (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                           (a: ptr) (esize ealign: SZ.t) (q: ptr)
                           (#p: perm) (#xs: Seq.seq t)
                           (w: SZ.t { SZ.v esize == 1 /\ word_in a q xs (SZ.v w) })
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  requires pure (bytelike t_repr ev ef)
  ensures  array_pts_to t_repr 1 (SZ.v ealign) a p (Seq.slice xs 0 (walk_idx 1 a q))
  ensures  exists* b. mem_pts_to q p b **
             pure (len b == SZ.v w /\ plain b /\ bytes_nat b < pow2 (8 * SZ.v w) /\
                   b == encode (SZ.v w) None (bytes_nat b) /\
                   word_bytes ev xs (walk_idx 1 a q) (SZ.v w) (bytes_nat b))
  ensures  array_pts_to t_repr 1 (SZ.v ealign) (q +! w) p
                        (Seq.slice xs (walk_idx 1 a q + SZ.v w) (Seq.length xs))
  ensures  pure (SZ.fits (addr_of a + Seq.length xs) /\ addr_of a + Seq.length xs < T.addr_limit /\
                 array_aligned 1 (SZ.v ealign) q)
{
  array_fits t_repr a esize ealign;
  assert (pure (SZ.fits (addr_of a + Seq.length xs) /\ addr_of a + Seq.length xs < T.addr_limit));
  let i : erased nat = walk_idx 1 a q;
  assert (pure (reveal i + SZ.v w <= Seq.length xs));
  SZ.fits_lte i (addr_of a + Seq.length xs);
  let isz = SZ.uint_to_t i;
  assert (pure (SZ.v isz == walk_idx 1 a q));
  rewrite (array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs)
       as (array_pts_to t_repr 1 (SZ.v ealign) a p xs);
  array_split t_repr a 1sz ealign #p #xs isz isz;
  walk_here a q (Seq.length xs) isz;
  rewrite each (a +! isz) as q;
  let rest : erased (Seq.seq t) = Seq.slice xs i (Seq.length xs);
  array_split t_repr q 1sz ealign #p #rest w w;
  Seq.slice_slice xs i (Seq.length xs) 0 (SZ.v w);
  Seq.slice_slice xs i (Seq.length xs) (SZ.v w) (Seq.length xs - i);
  let mid : erased (Seq.seq t) = Seq.slice xs i (i + SZ.v w);
  rewrite (array_pts_to t_repr 1 (SZ.v ealign) q p (Seq.slice rest 0 (SZ.v w)))
       as (array_pts_to t_repr 1 (SZ.v ealign) q p mid);
  rewrite (array_pts_to t_repr 1 (SZ.v ealign) (q +! w) p
                        (Seq.slice rest (SZ.v w) (Seq.length rest)))
       as (array_pts_to t_repr 1 (SZ.v ealign) (q +! w) p
                        (Seq.slice xs (walk_idx 1 a q + SZ.v w) (Seq.length xs)));
  unfold array_pts_to t_repr 1 (SZ.v ealign) q p mid;
  with b. assert (mem_pts_to q p b);
  elems_word t_repr ev ef mid b;
  word_bytes_slice ev xs i (SZ.v w) (bytes_nat b);
  assert (pure (len b == SZ.v w));
  assert (pure (plain b /\ bytes_nat b < pow2 (8 * SZ.v w)));
  assert (pure (b == encode (SZ.v w) None (bytes_nat b)));
  assert (pure (word_bytes ev xs (walk_idx 1 a q) (SZ.v w) (bytes_nat b)));
  assert (pure (array_aligned 1 (SZ.v ealign) q));
  rewrite (array_pts_to t_repr (SZ.v 1sz) (SZ.v ealign) a p (Seq.slice xs 0 (SZ.v isz)))
       as (array_pts_to t_repr 1 (SZ.v ealign) a p (Seq.slice xs 0 (walk_idx 1 a q)));
}

#push-options "--z3rlimit 20"
ghost fn array_bytes_unfocus (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                             (a: ptr) (esize ealign: SZ.t) (q: ptr)
                             (#p: perm) (#xs: Seq.seq t)
                             (w: SZ.t { SZ.v esize == 1 /\ word_in a q xs (SZ.v w) })
                             (ys: Seq.seq t) (x: nat)
  requires array_pts_to t_repr 1 (SZ.v ealign) a p (Seq.slice xs 0 (walk_idx 1 a q))
  requires mem_pts_to q p (encode (SZ.v w) None x)
  requires array_pts_to t_repr 1 (SZ.v ealign) (q +! w) p
                        (Seq.slice xs (walk_idx 1 a q + SZ.v w) (Seq.length xs))
  requires pure (bytelike t_repr ev ef /\
                 Seq.length ys == Seq.length xs /\ word_bytes ev ys (walk_idx 1 a q) (SZ.v w) x /\
                 (forall (k: nat). k < Seq.length xs /\ (k < walk_idx 1 a q \/ k >= walk_idx 1 a q + SZ.v w) ==>
                                   Seq.index ys k == Seq.index xs k) /\
                 SZ.fits (addr_of a + Seq.length xs) /\ addr_of a + Seq.length xs < T.addr_limit /\
                 array_aligned 1 (SZ.v ealign) q)
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p ys
{
  let i : erased nat = walk_idx 1 a q;
  assert (pure (reveal i + SZ.v w <= Seq.length xs));
  SZ.fits_lte i (addr_of a + Seq.length xs);
  let isz = SZ.uint_to_t i;
  assert (pure (SZ.v isz == walk_idx 1 a q));
  let mid : erased (Seq.seq t) = Seq.slice ys i (i + SZ.v w);
  word_bytes_slice ev ys i (SZ.v w) x;
  assert (pure (Seq.length mid == SZ.v w));
  assert (pure (word_bytes ev ys i (SZ.v w) x));
  assert (pure (word_bytes ev mid 0 (SZ.v w) x));
  assert (pure (word_bytes ev mid 0 (Seq.length mid) x));
  word_elems t_repr ev ef mid x;
  fold array_pts_to t_repr 1 (SZ.v ealign) q p mid;
  array_join t_repr q 1sz ealign w #p #mid;
  walk_here a q (Seq.length xs) isz;
  rewrite (array_pts_to t_repr (SZ.v 1sz) (SZ.v ealign) q p
             (Seq.append mid (Seq.slice xs (walk_idx 1 a q + SZ.v w) (Seq.length xs))))
       as (array_pts_to t_repr (SZ.v 1sz) (SZ.v ealign) (a +! isz) p
             (Seq.append mid (Seq.slice xs (i + SZ.v w) (Seq.length xs))));
  rewrite (array_pts_to t_repr 1 (SZ.v ealign) a p (Seq.slice xs 0 (walk_idx 1 a q)))
       as (array_pts_to t_repr (SZ.v 1sz) (SZ.v ealign) a p (Seq.slice xs 0 i));
  assert (pure (Seq.length (Seq.slice xs 0 i) == reveal i));
  join_off isz (Seq.slice xs 0 i);
  array_join t_repr a 1sz ealign isz #p #(Seq.slice xs 0 i)
    #(Seq.append mid (Seq.slice xs (i + SZ.v w) (Seq.length xs)));
  word_splice xs ys i (SZ.v w);
  rewrite (array_pts_to t_repr (SZ.v 1sz) (SZ.v ealign) a p
             (Seq.append (Seq.slice xs 0 i)
                         (Seq.append mid (Seq.slice xs (i + SZ.v w) (Seq.length xs)))))
       as (array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p ys);
}
#pop-options

(* ---------------------------------------------------------------------------
   Words of each unsigned integer type

   `focus` gives the word's own points-to, which the type's ordinary read and
   write work on; `unfocus_read` puts back a word that was only read, and
   `unfocus` one that may have been written, as the bytes of its new value.
   The alignment is asked for as arithmetic on the address, which is the form
   a `(uintptr_t)p % N` test in the source leaves behind.
   --------------------------------------------------------------------------- *)

(* `(uintptr_t)p` in a contract: the number the body's `ptr_to_uintptr`
   would observe, as a term. An address is below `addr_limit`, so it fits. *)
let uintptr_of (q: ptr) : GTot (n: SZ.t { SZ.v n == addr_of q }) =
  SZ.uint_to_t (addr_of q)

(* The same at `uint64_t`, which `uintptr_t` is on a 64-bit target: an
   address is below `addr_limit`, which is at most `pow2 64`. *)
let uintptr_u64 (q: ptr) : GTot (n: U64.t { U64.v n == addr_of q }) =
  FStar.Math.Lemmas.pow2_le_compat 64 32;
  U64.uint_to_t (addr_of q)

(* An alignment a loop invariant states survives a step by a multiple of it.
   The solver can show this itself, but modular arithmetic is where it is
   slowest, and a loop body has a large context. *)
let uintptr_of_step (q: ptr) (n: SZ.t) (m: pos)
  : Lemma (requires addr_of q + SZ.v n < T.addr_limit /\ SZ.v n % m == 0)
          (ensures  SZ.v (uintptr_of (q +! n)) % m == SZ.v (uintptr_of q) % m)
          [SMTPat (SZ.v (uintptr_of (q +! n)) % m)]
  = addr_of_add_nowrap q n;
    M.lemma_mod_add_distr (addr_of q) (SZ.v n) m

let uintptr_u64_step (q: ptr) (n: SZ.t) (m: pos)
  : Lemma (requires addr_of q + SZ.v n < T.addr_limit /\ SZ.v n % m == 0)
          (ensures  U64.v (uintptr_u64 (q +! n)) % m == U64.v (uintptr_u64 q) % m)
          [SMTPat (U64.v (uintptr_u64 (q +! n)) % m)]
  = addr_of_add_nowrap q n;
    M.lemma_mod_add_distr (addr_of q) (SZ.v n) m

(* The same in the form a contract's `(uintptr_t)w % ALIGN` takes when `ALIGN`
   is a `size_t` (`sizeof(size_t)`): the remainder is `SizeT.rem` of the
   address as a `size_t`, not `%` on the number. *)
let uintptr_rem_step (q: ptr) (n m: SZ.t)
  : Lemma (requires addr_of q + SZ.v n < T.addr_limit /\ SZ.v m > 0 /\ SZ.v n % SZ.v m == 0)
          (ensures  SZ.v (SZ.rem (sizet_of_uint64 (uintptr_u64 (q +! n))) m) ==
                    SZ.v (SZ.rem (sizet_of_uint64 (uintptr_u64 q)) m))
          [SMTPat (SZ.rem (sizet_of_uint64 (uintptr_u64 (q +! n))) m)]
  = uintptr_u64_step q n (SZ.v m)

let aligned_of_mod (q: ptr) (n: SZ.t)
  : Lemma (requires SZ.v n > 0 /\ addr_of q % SZ.v n == 0) (ensures aligned q n)
  = reveal_opaque (`%divides_addr) divides_addr

let word_value_uint16_t (b: bytes)
  : Lemma (requires len b == 2 /\ bytes_nat b < pow2 (8 * 2))
          (ensures  U16.v (uint16_t_of_bytes b) == bytes_nat b)
  = T.addr_limit_pow2 ();
    M.small_mod (bytes_nat b) (pow2 16)
(* `uint16_t` *)
ghost fn array_word_focus_uint16_t (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                             (bl: squash (bytelike t_repr ev ef))
                             (a: ptr) (esize ealign: SZ.t) (q: ptr) (#p: perm) (#xs: Seq.seq t)
                             (w: SZ.t { SZ.v w == 2 /\ SZ.v esize == 1 /\ word_in a q xs (SZ.v w) })
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  requires pure (addr_of q % SZ.v uint16_t_alignof == 0)
  ensures  array_pts_to t_repr 1 (SZ.v ealign) a p (Seq.slice xs 0 (walk_idx 1 a q))
  ensures  exists* x. uint16_t_pts_to q p x ** pure (word_bytes ev xs (walk_idx 1 a q) (SZ.v w) (U16.v x))
  ensures  array_pts_to t_repr 1 (SZ.v ealign) (q +! w) p
                        (Seq.slice xs (walk_idx 1 a q + SZ.v w) (Seq.length xs))
  ensures  pure (SZ.fits (addr_of a + Seq.length xs) /\ addr_of a + Seq.length xs < T.addr_limit /\
                 array_aligned 1 (SZ.v ealign) q)
{
  aligned_of_mod q uint16_t_alignof;
  array_bytes_focus t_repr ev ef a esize ealign q w;
  with b. assert (mem_pts_to q p b);
  word_value_uint16_t b;
  uint16_t_of_mem q;
}

ghost fn array_word_unfocus_read_uint16_t (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                                   (bl: squash (bytelike t_repr ev ef))
                                   (a: ptr) (esize ealign: SZ.t) (q: ptr) (#p: perm) (#xs: Seq.seq t)
                                   (w: SZ.t { SZ.v w == 2 /\ SZ.v esize == 1 /\ word_in a q xs (SZ.v w) })
                                   (#x: U16.t)
  requires array_pts_to t_repr 1 (SZ.v ealign) a p (Seq.slice xs 0 (walk_idx 1 a q))
  requires uint16_t_pts_to q p x
  requires array_pts_to t_repr 1 (SZ.v ealign) (q +! w) p
                        (Seq.slice xs (walk_idx 1 a q + SZ.v w) (Seq.length xs))
  requires pure (word_bytes ev xs (walk_idx 1 a q) (SZ.v w) (U16.v x) /\
                 SZ.fits (addr_of a + Seq.length xs) /\ addr_of a + Seq.length xs < T.addr_limit /\
                 array_aligned 1 (SZ.v ealign) q)
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
{
  uint16_t_to_mem q;
  rewrite (mem_pts_to q p (uint16_t_bytes x)) as (mem_pts_to q p (encode (SZ.v w) None (U16.v x)));
  array_bytes_unfocus t_repr ev ef a esize ealign q w xs (U16.v x);
}

ghost fn array_word_unfocus_uint16_t (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                              (bl: squash (bytelike t_repr ev ef))
                              (a: ptr) (esize ealign: SZ.t) (q: ptr) (#p: perm) (#xs: Seq.seq t)
                              (w: SZ.t { SZ.v w == 2 /\ SZ.v esize == 1 /\ word_in a q xs (SZ.v w) })
                              (#x: U16.t)
  requires array_pts_to t_repr 1 (SZ.v ealign) a p (Seq.slice xs 0 (walk_idx 1 a q))
  requires uint16_t_pts_to q p x
  requires array_pts_to t_repr 1 (SZ.v ealign) (q +! w) p
                        (Seq.slice xs (walk_idx 1 a q + SZ.v w) (Seq.length xs))
  requires pure (SZ.fits (addr_of a + Seq.length xs) /\ addr_of a + Seq.length xs < T.addr_limit /\
                 array_aligned 1 (SZ.v ealign) q)
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p
                        (word_upd ef xs (walk_idx 1 a q) (SZ.v w) (U16.v x))
{
  reveal_bytelike t_repr ev ef;
  uint16_t_to_mem q;
  rewrite (mem_pts_to q p (uint16_t_bytes x)) as (mem_pts_to q p (encode (SZ.v w) None (U16.v x)));
  array_bytes_unfocus t_repr ev ef a esize ealign q w
    (word_upd ef xs (walk_idx 1 a q) (SZ.v w) (U16.v x)) (U16.v x);
}

let word_value_uint32_t (b: bytes)
  : Lemma (requires len b == 4 /\ bytes_nat b < pow2 (8 * 4))
          (ensures  U32.v (uint32_t_of_bytes b) == bytes_nat b)
  = T.addr_limit_pow2 ();
    M.small_mod (bytes_nat b) (pow2 32)
(* `uint32_t` *)
ghost fn array_word_focus_uint32_t (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                             (bl: squash (bytelike t_repr ev ef))
                             (a: ptr) (esize ealign: SZ.t) (q: ptr) (#p: perm) (#xs: Seq.seq t)
                             (w: SZ.t { SZ.v w == 4 /\ SZ.v esize == 1 /\ word_in a q xs (SZ.v w) })
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  requires pure (addr_of q % SZ.v uint32_t_alignof == 0)
  ensures  array_pts_to t_repr 1 (SZ.v ealign) a p (Seq.slice xs 0 (walk_idx 1 a q))
  ensures  exists* x. uint32_t_pts_to q p x ** pure (word_bytes ev xs (walk_idx 1 a q) (SZ.v w) (U32.v x))
  ensures  array_pts_to t_repr 1 (SZ.v ealign) (q +! w) p
                        (Seq.slice xs (walk_idx 1 a q + SZ.v w) (Seq.length xs))
  ensures  pure (SZ.fits (addr_of a + Seq.length xs) /\ addr_of a + Seq.length xs < T.addr_limit /\
                 array_aligned 1 (SZ.v ealign) q)
{
  aligned_of_mod q uint32_t_alignof;
  array_bytes_focus t_repr ev ef a esize ealign q w;
  with b. assert (mem_pts_to q p b);
  word_value_uint32_t b;
  uint32_t_of_mem q;
}

ghost fn array_word_unfocus_read_uint32_t (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                                   (bl: squash (bytelike t_repr ev ef))
                                   (a: ptr) (esize ealign: SZ.t) (q: ptr) (#p: perm) (#xs: Seq.seq t)
                                   (w: SZ.t { SZ.v w == 4 /\ SZ.v esize == 1 /\ word_in a q xs (SZ.v w) })
                                   (#x: U32.t)
  requires array_pts_to t_repr 1 (SZ.v ealign) a p (Seq.slice xs 0 (walk_idx 1 a q))
  requires uint32_t_pts_to q p x
  requires array_pts_to t_repr 1 (SZ.v ealign) (q +! w) p
                        (Seq.slice xs (walk_idx 1 a q + SZ.v w) (Seq.length xs))
  requires pure (word_bytes ev xs (walk_idx 1 a q) (SZ.v w) (U32.v x) /\
                 SZ.fits (addr_of a + Seq.length xs) /\ addr_of a + Seq.length xs < T.addr_limit /\
                 array_aligned 1 (SZ.v ealign) q)
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
{
  uint32_t_to_mem q;
  rewrite (mem_pts_to q p (uint32_t_bytes x)) as (mem_pts_to q p (encode (SZ.v w) None (U32.v x)));
  array_bytes_unfocus t_repr ev ef a esize ealign q w xs (U32.v x);
}

ghost fn array_word_unfocus_uint32_t (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                              (bl: squash (bytelike t_repr ev ef))
                              (a: ptr) (esize ealign: SZ.t) (q: ptr) (#p: perm) (#xs: Seq.seq t)
                              (w: SZ.t { SZ.v w == 4 /\ SZ.v esize == 1 /\ word_in a q xs (SZ.v w) })
                              (#x: U32.t)
  requires array_pts_to t_repr 1 (SZ.v ealign) a p (Seq.slice xs 0 (walk_idx 1 a q))
  requires uint32_t_pts_to q p x
  requires array_pts_to t_repr 1 (SZ.v ealign) (q +! w) p
                        (Seq.slice xs (walk_idx 1 a q + SZ.v w) (Seq.length xs))
  requires pure (SZ.fits (addr_of a + Seq.length xs) /\ addr_of a + Seq.length xs < T.addr_limit /\
                 array_aligned 1 (SZ.v ealign) q)
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p
                        (word_upd ef xs (walk_idx 1 a q) (SZ.v w) (U32.v x))
{
  reveal_bytelike t_repr ev ef;
  uint32_t_to_mem q;
  rewrite (mem_pts_to q p (uint32_t_bytes x)) as (mem_pts_to q p (encode (SZ.v w) None (U32.v x)));
  array_bytes_unfocus t_repr ev ef a esize ealign q w
    (word_upd ef xs (walk_idx 1 a q) (SZ.v w) (U32.v x)) (U32.v x);
}

let word_value_uint64_t (b: bytes)
  : Lemma (requires len b == 8 /\ bytes_nat b < pow2 (8 * 8))
          (ensures  U64.v (uint64_t_of_bytes b) == bytes_nat b)
  = T.addr_limit_pow2 ();
    M.small_mod (bytes_nat b) (pow2 64)
(* `uint64_t` *)
ghost fn array_word_focus_uint64_t (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                             (bl: squash (bytelike t_repr ev ef))
                             (a: ptr) (esize ealign: SZ.t) (q: ptr) (#p: perm) (#xs: Seq.seq t)
                             (w: SZ.t { SZ.v w == 8 /\ SZ.v esize == 1 /\ word_in a q xs (SZ.v w) })
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  requires pure (addr_of q % SZ.v uint64_t_alignof == 0)
  ensures  array_pts_to t_repr 1 (SZ.v ealign) a p (Seq.slice xs 0 (walk_idx 1 a q))
  ensures  exists* x. uint64_t_pts_to q p x ** pure (word_bytes ev xs (walk_idx 1 a q) (SZ.v w) (U64.v x))
  ensures  array_pts_to t_repr 1 (SZ.v ealign) (q +! w) p
                        (Seq.slice xs (walk_idx 1 a q + SZ.v w) (Seq.length xs))
  ensures  pure (SZ.fits (addr_of a + Seq.length xs) /\ addr_of a + Seq.length xs < T.addr_limit /\
                 array_aligned 1 (SZ.v ealign) q)
{
  aligned_of_mod q uint64_t_alignof;
  array_bytes_focus t_repr ev ef a esize ealign q w;
  with b. assert (mem_pts_to q p b);
  word_value_uint64_t b;
  uint64_t_of_mem q;
}

ghost fn array_word_unfocus_read_uint64_t (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                                   (bl: squash (bytelike t_repr ev ef))
                                   (a: ptr) (esize ealign: SZ.t) (q: ptr) (#p: perm) (#xs: Seq.seq t)
                                   (w: SZ.t { SZ.v w == 8 /\ SZ.v esize == 1 /\ word_in a q xs (SZ.v w) })
                                   (#x: U64.t)
  requires array_pts_to t_repr 1 (SZ.v ealign) a p (Seq.slice xs 0 (walk_idx 1 a q))
  requires uint64_t_pts_to q p x
  requires array_pts_to t_repr 1 (SZ.v ealign) (q +! w) p
                        (Seq.slice xs (walk_idx 1 a q + SZ.v w) (Seq.length xs))
  requires pure (word_bytes ev xs (walk_idx 1 a q) (SZ.v w) (U64.v x) /\
                 SZ.fits (addr_of a + Seq.length xs) /\ addr_of a + Seq.length xs < T.addr_limit /\
                 array_aligned 1 (SZ.v ealign) q)
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
{
  uint64_t_to_mem q;
  rewrite (mem_pts_to q p (uint64_t_bytes x)) as (mem_pts_to q p (encode (SZ.v w) None (U64.v x)));
  array_bytes_unfocus t_repr ev ef a esize ealign q w xs (U64.v x);
}

ghost fn array_word_unfocus_uint64_t (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                              (bl: squash (bytelike t_repr ev ef))
                              (a: ptr) (esize ealign: SZ.t) (q: ptr) (#p: perm) (#xs: Seq.seq t)
                              (w: SZ.t { SZ.v w == 8 /\ SZ.v esize == 1 /\ word_in a q xs (SZ.v w) })
                              (#x: U64.t)
  requires array_pts_to t_repr 1 (SZ.v ealign) a p (Seq.slice xs 0 (walk_idx 1 a q))
  requires uint64_t_pts_to q p x
  requires array_pts_to t_repr 1 (SZ.v ealign) (q +! w) p
                        (Seq.slice xs (walk_idx 1 a q + SZ.v w) (Seq.length xs))
  requires pure (SZ.fits (addr_of a + Seq.length xs) /\ addr_of a + Seq.length xs < T.addr_limit /\
                 array_aligned 1 (SZ.v ealign) q)
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p
                        (word_upd ef xs (walk_idx 1 a q) (SZ.v w) (U64.v x))
{
  reveal_bytelike t_repr ev ef;
  uint64_t_to_mem q;
  rewrite (mem_pts_to q p (uint64_t_bytes x)) as (mem_pts_to q p (encode (SZ.v w) None (U64.v x)));
  array_bytes_unfocus t_repr ev ef a esize ealign q w
    (word_upd ef xs (walk_idx 1 a q) (SZ.v w) (U64.v x)) (U64.v x);
}

let word_value_size_t (b: bytes)
  : Lemma (requires len b == SZ.v size_t_sizeof /\ bytes_nat b < pow2 (8 * SZ.v size_t_sizeof))
          (ensures  SZ.v (size_t_of_bytes b) == bytes_nat b)
  = T.addr_limit_pow2 ();
    M.small_mod (bytes_nat b) (T.addr_limit)
(* `size_t` *)
ghost fn array_word_focus_size_t (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                             (bl: squash (bytelike t_repr ev ef))
                             (a: ptr) (esize ealign: SZ.t) (q: ptr) (#p: perm) (#xs: Seq.seq t)
                             (w: SZ.t { SZ.v w == SZ.v size_t_sizeof /\ SZ.v esize == 1 /\ word_in a q xs (SZ.v w) })
  requires array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
  requires pure (addr_of q % SZ.v size_t_alignof == 0)
  ensures  array_pts_to t_repr 1 (SZ.v ealign) a p (Seq.slice xs 0 (walk_idx 1 a q))
  ensures  exists* x. size_t_pts_to q p x ** pure (word_bytes ev xs (walk_idx 1 a q) (SZ.v w) (SZ.v x))
  ensures  array_pts_to t_repr 1 (SZ.v ealign) (q +! w) p
                        (Seq.slice xs (walk_idx 1 a q + SZ.v w) (Seq.length xs))
  ensures  pure (SZ.fits (addr_of a + Seq.length xs) /\ addr_of a + Seq.length xs < T.addr_limit /\
                 array_aligned 1 (SZ.v ealign) q)
{
  aligned_of_mod q size_t_alignof;
  array_bytes_focus t_repr ev ef a esize ealign q w;
  with b. assert (mem_pts_to q p b);
  word_value_size_t b;
  size_t_of_mem q;
}

ghost fn array_word_unfocus_read_size_t (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                                   (bl: squash (bytelike t_repr ev ef))
                                   (a: ptr) (esize ealign: SZ.t) (q: ptr) (#p: perm) (#xs: Seq.seq t)
                                   (w: SZ.t { SZ.v w == SZ.v size_t_sizeof /\ SZ.v esize == 1 /\ word_in a q xs (SZ.v w) })
                                   (#x: SZ.t)
  requires array_pts_to t_repr 1 (SZ.v ealign) a p (Seq.slice xs 0 (walk_idx 1 a q))
  requires size_t_pts_to q p x
  requires array_pts_to t_repr 1 (SZ.v ealign) (q +! w) p
                        (Seq.slice xs (walk_idx 1 a q + SZ.v w) (Seq.length xs))
  requires pure (word_bytes ev xs (walk_idx 1 a q) (SZ.v w) (SZ.v x) /\
                 SZ.fits (addr_of a + Seq.length xs) /\ addr_of a + Seq.length xs < T.addr_limit /\
                 array_aligned 1 (SZ.v ealign) q)
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p xs
{
  size_t_to_mem q;
  rewrite (mem_pts_to q p (size_t_bytes x)) as (mem_pts_to q p (encode (SZ.v w) None (SZ.v x)));
  array_bytes_unfocus t_repr ev ef a esize ealign q w xs (SZ.v x);
}

ghost fn array_word_unfocus_size_t (#t: Type0) (t_repr: t -> bytes -> prop) (ev: t -> nat) (ef: nat -> t)
                              (bl: squash (bytelike t_repr ev ef))
                              (a: ptr) (esize ealign: SZ.t) (q: ptr) (#p: perm) (#xs: Seq.seq t)
                              (w: SZ.t { SZ.v w == SZ.v size_t_sizeof /\ SZ.v esize == 1 /\ word_in a q xs (SZ.v w) })
                              (#x: SZ.t)
  requires array_pts_to t_repr 1 (SZ.v ealign) a p (Seq.slice xs 0 (walk_idx 1 a q))
  requires size_t_pts_to q p x
  requires array_pts_to t_repr 1 (SZ.v ealign) (q +! w) p
                        (Seq.slice xs (walk_idx 1 a q + SZ.v w) (Seq.length xs))
  requires pure (SZ.fits (addr_of a + Seq.length xs) /\ addr_of a + Seq.length xs < T.addr_limit /\
                 array_aligned 1 (SZ.v ealign) q)
  ensures  array_pts_to t_repr (SZ.v esize) (SZ.v ealign) a p
                        (word_upd ef xs (walk_idx 1 a q) (SZ.v w) (SZ.v x))
{
  reveal_bytelike t_repr ev ef;
  size_t_to_mem q;
  rewrite (mem_pts_to q p (size_t_bytes x)) as (mem_pts_to q p (encode (SZ.v w) None (SZ.v x)));
  array_bytes_unfocus t_repr ev ef a esize ealign q w
    (word_upd ef xs (walk_idx 1 a q) (SZ.v w) (SZ.v x)) (SZ.v x);
}

(* An element read inside a word, at whatever index a quantified contract
   reads it: nothing it sees mentions `Seq.index xs (i + j)`. *)
let word_bytes_at (#t: Type0) (ev: t -> nat) (xs: Seq.seq t) (i: nat) (w: nat) (x: nat) (k: nat)
  : Lemma (requires word_bytes ev xs i w x /\ i <= k /\ k < i + w)
          (ensures  ev (Seq.index xs k) == word_byte w x (k - i))
          [SMTPat (word_bytes ev xs i w x); SMTPat (Seq.index xs k)]
  = reveal_word_bytes ev xs i w x;
    assert (ev (Seq.index xs (i + (k - i))) == word_byte w x (k - i))

let word_bytes_upto_at (#t: Type0) (ev: t -> nat) (xs: Seq.seq t) (i: nat) (w: nat) (x: nat) (k: nat)
  : Lemma (requires word_bytes_upto ev xs i w x /\ i <= k /\ k < i + w /\ k < Seq.length xs)
          (ensures  ev (Seq.index xs k) == word_byte w x (k - i))
          [SMTPat (word_bytes_upto ev xs i w x); SMTPat (Seq.index xs k)]
  = reveal_word_bytes_upto ev xs i w x;
    assert (ev (Seq.index xs (i + (k - i))) == word_byte w x (k - i))

(* ---------------------------------------------------------------------------
   `char` arrays as `unsigned char` arrays
   --------------------------------------------------------------------------- *)

(* A `char` (`signed char`) and the `unsigned char` it converts to are the
   same byte, so an array of one is an array of the other: this is what lets
   a `char *` be passed where a `void *` array -- an array of `unsigned char`
   -- is wanted (`memchr(s, c, n)`), and taken back afterwards. *)
let int8_as_uint8_repr (x: I8.t) (b: bytes)
  : Lemma (requires int8_t_repr x b)
          (ensures  uint8_t_repr (FStar.Int.Cast.int8_to_uint8 x) b)
  = assert_norm (pow2 8 == 256);
    assert_norm (pow2 7 == 128)

let uint8_as_int8_repr (x: U8.t) (b: bytes)
  : Lemma (requires uint8_t_repr x b)
          (ensures  int8_t_repr (FStar.Int.Cast.uint8_to_int8 x) b)
  = assert_norm (pow2 8 == 256);
    assert_norm (pow2 7 == 128)

let int8_uint8_inverse (_: unit)
  : Lemma ((forall (x: I8.t). FStar.Int.Cast.uint8_to_int8 (FStar.Int.Cast.int8_to_uint8 x) == x) /\
           (forall (x: U8.t). FStar.Int.Cast.int8_to_uint8 (FStar.Int.Cast.uint8_to_int8 x) == x))
  = assert_norm (pow2 8 == 256);
    assert_norm (pow2 7 == 128);
    let aux1 (x: I8.t)
      : Lemma (FStar.Int.Cast.uint8_to_int8 (FStar.Int.Cast.int8_to_uint8 x) == x)
      = I8.v_inj (FStar.Int.Cast.uint8_to_int8 (FStar.Int.Cast.int8_to_uint8 x)) x in
    let aux2 (x: U8.t)
      : Lemma (FStar.Int.Cast.int8_to_uint8 (FStar.Int.Cast.uint8_to_int8 x) == x)
      = U8.v_inj (FStar.Int.Cast.int8_to_uint8 (FStar.Int.Cast.uint8_to_int8 x)) x in
    FStar.Classical.forall_intro aux1;
    FStar.Classical.forall_intro aux2

let seq_int8_uint8_back (xs: Seq.seq I8.t)
  : Lemma (seq_map FStar.Int.Cast.uint8_to_int8 (seq_map FStar.Int.Cast.int8_to_uint8 xs) == xs)
          [SMTPat (seq_map FStar.Int.Cast.uint8_to_int8 (seq_map FStar.Int.Cast.int8_to_uint8 xs))]
  = int8_uint8_inverse ();
    seq_map_inverse FStar.Int.Cast.int8_to_uint8 FStar.Int.Cast.uint8_to_int8 xs

ghost fn array_int8_as_uint8 (a: ptr) (#p: perm) (#xs: Seq.seq I8.t)
  requires array_pts_to int8_t_repr 1 (SZ.v int8_t_alignof) a p xs
  ensures  array_pts_to uint8_t_repr 1 (SZ.v uint8_t_alignof) a p
             (seq_map FStar.Int.Cast.int8_to_uint8 xs)
{
  FStar.Classical.forall_intro_2 (fun x -> FStar.Classical.move_requires (int8_as_uint8_repr x));
  array_retype int8_t_repr uint8_t_repr FStar.Int.Cast.int8_to_uint8 a 1sz int8_t_alignof;
  rewrite each (SZ.v int8_t_alignof) as (SZ.v uint8_t_alignof);
}

ghost fn array_uint8_as_int8 (a: ptr) (#p: perm) (#ys: Seq.seq U8.t)
  requires array_pts_to uint8_t_repr 1 (SZ.v uint8_t_alignof) a p ys
  ensures  array_pts_to int8_t_repr 1 (SZ.v int8_t_alignof) a p
             (seq_map FStar.Int.Cast.uint8_to_int8 ys)
{
  FStar.Classical.forall_intro_2 (fun x -> FStar.Classical.move_requires (uint8_as_int8_repr x));
  array_retype uint8_t_repr int8_t_repr FStar.Int.Cast.uint8_to_int8 a 1sz uint8_t_alignof;
  rewrite each (SZ.v uint8_t_alignof) as (SZ.v int8_t_alignof);
}
