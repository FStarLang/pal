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

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let rec decode_encode (n: nat) (p: prov) (x: nat)
  : Lemma (ensures decode (encode n p x) == Some (x % pow2 (8 * n)))
          (decreases n)
  = assert_norm (pow2 8 == 256);
    assert_norm (pow2 0 == 1);
    if n = 0 then ()
    else begin
      let b = encode n p x in
      let m = pow2 (8 * (n - 1)) in
      assert ((get b 0).value == Some (U8.uint_to_t (x % 256)));
      encode_tail n p x;
      decode_encode (n - 1) p (x / 256);
      assert (decode (slice b 1 (len b)) == Some ((x / 256) % m));
      assert (decode b == Some (x % 256 + 256 * ((x / 256) % m)));
      M.pow2_plus 8 (8 * (n - 1));
      assert (pow2 (8 * n) == 256 * m);
      M.modulo_division_lemma x 256 m;
      M.modulo_modulo_lemma x 256 m;
      M.euclidean_division_definition (x % (256 * m)) 256
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
