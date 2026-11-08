module Pulse.Lib.C.Palow.Encoding

(* ---------------------------------------------------------------------------
   Object representations of unsigned integers.

   This is the concrete witness that Palow's `*_repr` relations can be
   *defined* rather than axiomatized. `encode_le n p x` is the `n`-byte
   little-endian representation of `x`, with every byte tagged with provenance
   `p`; `decode_le` is its partial inverse, undefined (`None`) when any covered
   byte is uninitialized.

   The representation the rest of Palow uses is `encode`/`decode` at the end of
   this module, which put the bytes in the target's order. The byte order is
   `Target.little_endian`, abstract here, so everything this module proves
   holds on either kind of target -- see `palow.md`.
   --------------------------------------------------------------------------- *)

open Pulse.Lib.C.Palow.Bytes
module Seq = FStar.Seq
module U8 = FStar.UInt8
module M = FStar.Math.Lemmas
module T = Pulse.Lib.C.Palow.Target

let byte_at (p: prov) (x: nat) (i: nat) : byte =
  { value = Some (U8.uint_to_t ((x / pow2 (8 * i)) % 256)); prov = p }

let encode_le (n: nat) (p: prov) (x: nat) : b:bytes { len b == n } =
  Seq.init n (byte_at p x)

let encode_le_index (n: nat) (p: prov) (x: nat) (i: nat)
  : Lemma (requires i < n)
          (ensures  get (encode_le n p x) i == byte_at p x i)
          [SMTPat (get (encode_le n p x) i)]
  = ()

let encode_le_has_prov (n: nat) (p: prov) (x: nat)
  : Lemma (has_prov p (encode_le n p x) /\ initialized (encode_le n p x))
          [SMTPat (encode_le n p x)]
  = ()

let rec decode_le (b: bytes) : Tot (option nat) (decreases (len b)) =
  if len b = 0 then Some 0
  else match (get b 0).value with
       | None -> None
       | Some v ->
         (match decode_le (slice b 1 (len b)) with
          | None -> None
          | Some r -> Some (U8.v v + 256 * r))

(* Dropping the first byte of an `n`-byte encoding of `x` leaves the
   `(n-1)`-byte encoding of `x / 256`: the induction step for `decode_encode_le`. *)
#push-options "--z3rlimit 30"
let encode_le_tail (n: nat { n > 0 }) (p: prov) (x: nat)
  : Lemma (slice (encode_le n p x) 1 n == encode_le (n - 1) p (x / 256))
  = let lhs = slice (encode_le n p x) 1 n in
    let rhs = encode_le (n - 1) p (x / 256) in
    assert_norm (pow2 8 == 256);
    let aux (i: nat { i < n - 1 }) : Lemma (get lhs i == get rhs i) =
      Seq.lemma_index_slice (encode_le n p x) 1 n i;
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
   `1`, but saying so inside `decode_encode_le` costs a query with the induction
   hypothesis and the whole `encode_le`/`decode_le` axiomatization in context. Here
   there is nothing to search. *)
let encode_le_head (n: nat { n > 0 }) (p: prov) (x: nat)
  : Lemma ((get (encode_le n p x) 0).value == Some (U8.uint_to_t (x % 256)))
  = assert_norm (pow2 (8 * 0) == 1)

(* The arithmetic core of `decode_encode_le`, with no bytes in sight: splitting a
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
let rec decode_encode_le (n: nat) (p: prov) (x: nat)
  : Lemma (ensures decode_le (encode_le n p x) == Some (x % pow2 (8 * n)))
          (decreases n)
  = if n = 0 then assert_norm (pow2 (8 * 0) == 1)
    else begin
      encode_le_head n p x;
      encode_le_tail n p x;
      decode_encode_le (n - 1) p (x / 256);
      pow2_step n;
      mod_split x (pow2 (8 * (n - 1)))
    end
#pop-options

let decode_encode_le_exact (n: nat) (p: prov) (x: nat { x < pow2 (8 * n) })
  : Lemma (decode_le (encode_le n p x) == Some x)
  = decode_encode_le n p x;
    M.small_mod x (pow2 (8 * n))

(* `encode_le` is injective in the value, which is what gives the scalar typed
   points-to predicates their agreement lemma. It is *not* injective in the
   provenance-erased sense: two encodings differing only in provenance are
   different byte ranges, which is exactly what we want, since a stored pointer
   and an integer with the same bit pattern are not interchangeable. *)
let encode_le_injective (n: nat) (p: prov) (x y: nat)
  : Lemma (requires x < pow2 (8 * n) /\ y < pow2 (8 * n) /\ encode_le n p x == encode_le n p y)
          (ensures  x == y)
  = decode_encode_le_exact n p x;
    decode_encode_le_exact n p y


(* The value a plain range encodes, little-endian. `decode_le` is partial only
   on uninitialised bytes, so on an initialised range the default is never
   taken. *)
let bytes_nat_le (b: bytes) : nat =
  match decode_le b with Some x -> x | None -> 0

let decode_le_cons (b: bytes)
  : Lemma (requires len b > 0)
          (ensures  decode_le b ==
                    (match (get b 0).value with
                     | None -> None
                     | Some v ->
                       (match decode_le (slice b 1 (len b)) with
                        | None -> None
                        | Some r -> Some (U8.v v + 256 * r))))
  = assert_norm (decode_le b ==
                    (if len b = 0 then Some 0 else
                     match (get b 0).value with
                     | None -> None
                     | Some v ->
                       (match decode_le (slice b 1 (len b)) with
                        | None -> None
                        | Some r -> Some (U8.v v + 256 * r))))

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec encode_decode_le (b: bytes)
  : Lemma (requires initialized b /\ no_prov b)
          (ensures  bytes_nat_le b < pow2 (8 * len b) /\
                    b == encode_le (len b) None (bytes_nat_le b))
          (decreases (len b))
  = if len b = 0 then begin
      assert_norm (pow2 (8 * 0) == 1);
      Seq.lemma_eq_intro b (encode_le 0 None 0)
    end else begin
      let n = len b in
      let tl = slice b 1 n in
      encode_decode_le tl;
      let r = bytes_nat_le tl in
      decode_encode_le_exact (n - 1) None r;
      assert (decode_le tl == Some r);
      assert (Some? (get b 0).value);
      let v0 = Some?.v (get b 0).value in
      decode_le_cons b;
      assert (decode_le b == Some (U8.v v0 + 256 * r));
      let x = U8.v v0 + 256 * r in
      pow2_step n;
      assert (x < pow2 (8 * n));
      encode_le_head n None x;
      encode_le_tail n None x;
      M.lemma_mod_plus (U8.v v0) r 256;
      M.small_mod (U8.v v0) 256;
      M.lemma_div_plus (U8.v v0) r 256;
      M.small_div (U8.v v0) 256;
      let e = encode_le n None x in
      assert (slice e 1 n == encode_le (n - 1) None r);
      let aux (i: nat { i < n }) : Lemma (get b i == get e i) =
        if i = 0 then ()
        else begin
          let j : nat = i - 1 in
          assert (get b i == get tl j);
          assert (get e i == get (slice e 1 n) j)
        end
      in
      Classical.forall_intro aux;
      Seq.lemma_eq_intro b e
    end
#pop-options

(* ---------------------------------------------------------------------------
   The target's byte order

   `encode` and `decode` are the representation the rest of Palow uses. They
   are the little-endian ones above on a little-endian target and their byte
   reversal on a big-endian one, and which of the two it is is
   `Target.little_endian`, which the library never fixes. Everything below is
   proved for both, so a fact about representations that does not depend on
   the byte order is provable without saying what it is.
   --------------------------------------------------------------------------- *)

let rev (b: bytes) : b':bytes { len b' == len b } =
  Seq.init (len b) (fun (i: nat { i < len b }) -> get b (len b - 1 - i))

let rev_index (b: bytes) (i: nat { i < len b })
  : Lemma (get (rev b) i == get b (len b - 1 - i))
          [SMTPat (get (rev b) i)]
  = ()

let rev_rev (b: bytes) : Lemma (rev (rev b) == b) =
  bytes_ext (rev (rev b)) b

let rev_injective (b1 b2: bytes)
  : Lemma (requires rev b1 == rev b2) (ensures b1 == b2)
  = rev_rev b1; rev_rev b2

let rev_initialized (b: bytes)
  : Lemma (requires initialized b) (ensures initialized (rev b))
  = ()

let rev_has_prov (p: prov) (b: bytes)
  : Lemma (requires has_prov p b) (ensures has_prov p (rev b))
  = ()

let encode (n: nat) (p: prov) (x: nat) : b:bytes { len b == n } =
  if T.little_endian then encode_le n p x else rev (encode_le n p x)

let decode (b: bytes) : option nat =
  if T.little_endian then decode_le b else decode_le (rev b)

(* Which byte of the value lands at position `i` of an `n`-byte
   representation: the `i`-th least significant on a little-endian target, the
   `i`-th most significant on a big-endian one. *)
let byte_index (n: nat) (i: nat { i < n }) : j:nat { j < n } =
  if T.little_endian then i else n - 1 - i

let encode_index (n: nat) (p: prov) (x: nat) (i: nat)
  : Lemma (requires i < n)
          (ensures  get (encode n p x) i == byte_at p x (byte_index n i))
          [SMTPat (get (encode n p x) i)]
  = ()

let encode_has_prov (n: nat) (p: prov) (x: nat)
  : Lemma (has_prov p (encode n p x) /\ initialized (encode n p x))
          [SMTPat (encode n p x)]
  = ()

let decode_encode (n: nat) (p: prov) (x: nat)
  : Lemma (decode (encode n p x) == Some (x % pow2 (8 * n)))
  = decode_encode_le n p x;
    rev_rev (encode_le n p x)

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

(* The value an initialised, provenance-free range encodes. *)
let bytes_nat (b: bytes) : nat =
  match decode b with Some x -> x | None -> 0

(* Every initialised, provenance-free range is the encoding of exactly one
   value: the one it decodes to. *)
let encode_decode (b: bytes)
  : Lemma (requires initialized b /\ no_prov b)
          (ensures  decode b == Some (bytes_nat b) /\
                    bytes_nat b < pow2 (8 * len b) /\
                    b == encode (len b) None (bytes_nat b))
  = if T.little_endian then begin
      encode_decode_le b;
      decode_encode_le_exact (len b) None (bytes_nat_le b)
    end else begin
      let r = rev b in
      encode_decode_le r;
      decode_encode_le_exact (len b) None (bytes_nat_le r);
      rev_rev b
    end

(* An all-zero range is the encoding of the value zero, at any width and in
   either byte order. *)
let encode_zero (n: nat)
  : Lemma (encode n None 0 == zeroed n)
  = assert_norm (forall (i: nat). (0 / pow2 (8 * i)) % 256 == 0);
    bytes_ext (encode n None 0) (zeroed n)


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
