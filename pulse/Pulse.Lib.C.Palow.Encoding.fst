module Pulse.Lib.C.Palow.Encoding

(* ---------------------------------------------------------------------------
   Object representations of unsigned integers.

   This is the concrete witness that Palow's `*_repr` relations can be
   *defined* rather than axiomatized. `encode n p x` is the `n`-byte
   little-endian representation of `x`, with every byte tagged with provenance
   `p`; `decode` is its partial inverse, undefined (`None`) when any covered
   byte is uninitialized.

   Endianness is fixed to little-endian here. That makes generated code
   target-dependent, but it already is (`long` is 64-bit on Linux and 32-bit on
   Windows), so this is not a new constraint -- see `palow.md`.
   --------------------------------------------------------------------------- *)

open Pulse.Lib.C.Palow.Bytes
module Seq = FStar.Seq
module U8 = FStar.UInt8
module M = FStar.Math.Lemmas

let byte_at (p: prov) (x: nat) (i: nat) : byte =
  { value = Some (U8.uint_to_t ((x / pow2 (8 * i)) % 256)); prov = p }

let encode (n: nat) (p: prov) (x: nat) : b:bytes { len b == n } =
  Seq.init n (byte_at p x)

let encode_index (n: nat) (p: prov) (x: nat) (i: nat)
  : Lemma (requires i < n)
          (ensures  get (encode n p x) i == byte_at p x i)
          [SMTPat (get (encode n p x) i)]
  = ()

let encode_has_prov (n: nat) (p: prov) (x: nat)
  : Lemma (has_prov p (encode n p x) /\ initialized (encode n p x))
          [SMTPat (encode n p x)]
  = ()

let rec decode (b: bytes) : Tot (option nat) (decreases (len b)) =
  if len b = 0 then Some 0
  else match (get b 0).value with
       | None -> None
       | Some v ->
         (match decode (slice b 1 (len b)) with
          | None -> None
          | Some r -> Some (U8.v v + 256 * r))

(* Dropping the first byte of an `n`-byte encoding of `x` leaves the
   `(n-1)`-byte encoding of `x / 256`: the induction step for `decode_encode`. *)
#push-options "--z3rlimit 30"
let encode_tail (n: nat { n > 0 }) (p: prov) (x: nat)
  : Lemma (slice (encode n p x) 1 n == encode (n - 1) p (x / 256))
  = let lhs = slice (encode n p x) 1 n in
    let rhs = encode (n - 1) p (x / 256) in
    assert_norm (pow2 8 == 256);
    let aux (i: nat { i < n - 1 }) : Lemma (get lhs i == get rhs i) =
      Seq.lemma_index_slice (encode n p x) 1 n i;
      assert (get lhs i == byte_at p x (i + 1));
      M.pow2_plus 8 (8 * i);
      assert (pow2 (8 * (i + 1)) == 256 * pow2 (8 * i));
      M.division_multiplication_lemma x 256 (pow2 (8 * i));
      assert (x / pow2 (8 * (i + 1)) == (x / 256) / pow2 (8 * i))
    in
    Classical.forall_intro aux;
    bytes_ext lhs rhs
#pop-options

(* The first byte of an encoding. It is `byte_at p x 0`, and `pow2 (8 * 0)` is
   `1`, but saying so inside `decode_encode` costs a query with the induction
   hypothesis and the whole `encode`/`decode` axiomatization in context. Here
   there is nothing to search. *)
let encode_head (n: nat { n > 0 }) (p: prov) (x: nat)
  : Lemma ((get (encode n p x) 0).value == Some (U8.uint_to_t (x % 256)))
  = assert_norm (pow2 (8 * 0) == 1)

(* The arithmetic core of `decode_encode`, with no bytes in sight: splitting a
   number modulo `256 * m` into its low byte and the rest. Stated over plain
   `nat`s because that is what it is about, and because the solver was
   previously proving it in a context full of sequences and quantified
   pointwise predicates, where the nonlinear steps below turn into a search. *)
#push-options "--z3rlimit 30"
let mod_split (x: nat) (m: pos)
  : Lemma (x % (256 * m) == x % 256 + 256 * ((x / 256) % m))
  = M.modulo_division_lemma x 256 m;
    M.modulo_modulo_lemma x 256 m;
    M.euclidean_division_definition (x % (256 * m)) 256
#pop-options

(* `pow2 (8 * n) == 256 * pow2 (8 * (n - 1))`. The exponent step `8 * n ==
   8 + 8 * (n - 1)` is linear, but left inside the `pow2` argument it makes
   `pow2_plus` a search rather than a rewrite. *)
let pow2_step (n: nat { n > 0 })
  : Lemma (pow2 (8 * n) == 256 * pow2 (8 * (n - 1)))
  = assert_norm (pow2 8 == 256);
    assert (8 * n == 8 + 8 * (n - 1));
    M.pow2_plus 8 (8 * (n - 1))

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
let rec decode_encode (n: nat) (p: prov) (x: nat)
  : Lemma (ensures decode (encode n p x) == Some (x % pow2 (8 * n)))
          (decreases n)
  = if n = 0 then assert_norm (pow2 (8 * 0) == 1)
    else begin
      encode_head n p x;
      encode_tail n p x;
      decode_encode (n - 1) p (x / 256);
      pow2_step n;
      mod_split x (pow2 (8 * (n - 1)))
    end
#pop-options

let decode_encode_exact (n: nat) (p: prov) (x: nat { x < pow2 (8 * n) })
  : Lemma (decode (encode n p x) == Some x)
  = decode_encode n p x;
    M.small_mod x (pow2 (8 * n))

(* `encode` is injective in the value, which is what gives the scalar typed
   points-to predicates their agreement lemma. It is *not* injective in the
   provenance-erased sense: two encodings differing only in provenance are
   different byte ranges, which is exactly what we want, since a stored pointer
   and an integer with the same bit pattern are not interchangeable. *)
let encode_injective (n: nat) (p: prov) (x y: nat)
  : Lemma (requires x < pow2 (8 * n) /\ y < pow2 (8 * n) /\ encode n p x == encode n p y)
          (ensures  x == y)
  = decode_encode_exact n p x;
    decode_encode_exact n p y

(* ---------------------------------------------------------------------------
   Signed integers

   C leaves the signed representation implementation-defined, but every target
   PAL supports uses two's complement, and C23 mandates it. So a signed value
   is encoded as its non-negative residue: the same `encode` as an unsigned
   value of the same width, applied to `to_bits`.

   `to_bits` is stated on the bit width rather than the byte count because that
   is where the asymmetry of the signed range lives, and it carries the range
   through in its result type so that `encode` can be applied without a side
   condition at every use. *)
let to_bits (w: pos) (x: int { -(pow2 (w - 1)) <= x /\ x < pow2 (w - 1) })
  : n:nat { n < pow2 w }
  = M.pow2_double_sum (w - 1);
    if x < 0 then x + pow2 w else x

let to_bits_injective (w: pos)
                      (x: int { -(pow2 (w - 1)) <= x /\ x < pow2 (w - 1) })
                      (y: int { -(pow2 (w - 1)) <= y /\ y < pow2 (w - 1) })
  : Lemma (requires to_bits w x == to_bits w y)
          (ensures  x == y)
  = M.pow2_double_sum (w - 1)
