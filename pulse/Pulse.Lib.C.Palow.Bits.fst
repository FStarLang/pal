module Pulse.Lib.C.Palow.Bits

(* A bit-field is not an object. It has no address, no size and no storage of
   its own: what it has is a position inside the storage unit it shares with
   its neighbours. So the byte-level model does not give a bit-field a
   points-to at all. The unit is an ordinary unsigned integer object, with an
   ordinary byte representation, and each bit-field is a *function* of the
   unit's value -- the `w` bits starting at offset `o`.

   That is why this module is pure arithmetic and contains no slprop. A read
   of a bit-field is a read of the unit followed by `get`; a write is a read
   of the unit, a `put`, and a write back, which is exactly what a C compiler
   emits. The bits of the unit that belong to no bit-field are carried along
   in the unit's value, untouched and unconstrained, which is what C says
   about them.

   Everything is stated on `nat` first and then wrapped per machine width, so
   that the bounds proof happens once. *)

module M = FStar.Math.Lemmas

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

(* The `w` bits of `u` starting at bit `o`. *)
let get (u: nat) (o: nat) (w: nat) : n:nat { n < pow2 w } =
  (u / pow2 o) % pow2 w

(* `u` with those bits replaced by the low `w` bits of `x`. Written as a sum
   of three manifestly non-negative pieces -- the part above the field, the
   field, and the part below it -- so that it is a `nat` by construction. *)
let put (u: nat) (o: nat) (w: nat) (x: nat) : nat =
  (u / pow2 (o + w)) * pow2 (o + w) + (x % pow2 w) * pow2 o + u % pow2 o

(* The field occupies the bits it says it does, so the two pieces of `put`
   that are not the part above it stay below bit `o + w`. *)
let put_low (u: nat) (o: nat) (w: nat) (x: nat)
  : Lemma ((x % pow2 w) * pow2 o + u % pow2 o < pow2 (o + w))
  = M.pow2_plus o w;
    M.lemma_mult_le_right (pow2 o) (x % pow2 w) (pow2 w - 1);
    M.distributivity_sub_left (pow2 w) 1 (pow2 o)

(* What was put is what is read back. *)
let put_get (u: nat) (o: nat) (w: nat) (x: nat)
  : Lemma (get (put u o w x) o w == x % pow2 w)
          [SMTPat (get (put u o w x) o w)]
  = M.pow2_plus o w;
    put_low u o w x;
    let q = u / pow2 (o + w) in
    let f = x % pow2 w in
    let r = u % pow2 o in
    M.paren_mul_right q (pow2 o) (pow2 w);
    M.swap_mul (pow2 o) (pow2 w);
    M.paren_mul_right q (pow2 w) (pow2 o);
    M.distributivity_add_left (q * pow2 w) f (pow2 o);
    assert (put u o w x == r + (q * pow2 w + f) * pow2 o);
    M.lemma_div_plus r (q * pow2 w + f) (pow2 o);
    M.small_div r (pow2 o);
    assert (put u o w x / pow2 o == q * pow2 w + f);
    M.lemma_mod_plus f q (pow2 w);
    M.modulo_modulo_lemma x (pow2 w) 1

(* A unit stays inside its width: the field being written is inside it, and
   nothing else moves. *)
let put_bound (u: nat) (o: nat) (w: nat) (x: nat) (n: nat)
  : Lemma (requires u < pow2 n /\ o + w <= n)
          (ensures put u o w x < pow2 n)
  = put_low u o w x;
    M.pow2_plus (o + w) (n - o - w);
    let m = pow2 (o + w) in
    M.lemma_div_lt_nat u n (o + w);
    M.lemma_mult_le_right m (u / m) (pow2 (n - o - w) - 1);
    M.distributivity_sub_left (pow2 (n - o - w)) 1 m

(* Two units that agree below bit `k` agree on every field that ends at or
   before `k`. *)
let bits_below (a b: nat) (o: nat) (w: nat) (k: nat)
  : Lemma (requires o + w <= k /\ a % pow2 k == b % pow2 k)
          (ensures get a o w == get b o w)
  = M.pow2_modulo_division_lemma_1 a o (o + w);
    M.pow2_modulo_division_lemma_1 b o (o + w);
    M.pow2_plus (o + w) (k - o - w);
    M.modulo_modulo_lemma a (pow2 (o + w)) (pow2 (k - o - w));
    M.modulo_modulo_lemma b (pow2 (o + w)) (pow2 (k - o - w))

(* Two units that agree above bit `k` agree on every field that starts at or
   after `k`. *)
let bits_above (a b: nat) (o: nat) (w: nat) (k: nat)
  : Lemma (requires k <= o /\ a / pow2 k == b / pow2 k)
          (ensures get a o w == get b o w)
  = M.pow2_plus k (o - k);
    M.division_multiplication_lemma a (pow2 k) (pow2 (o - k));
    M.division_multiplication_lemma b (pow2 k) (pow2 (o - k))

(* Writing one field leaves the others alone. Only ever needed when a
   contract mentions a neighbour of the field being written, but a model in
   which that were not provable would not be worth much. *)
let put_frame (u: nat) (o1: nat) (w1: nat) (o2: nat) (w2: nat) (x: nat)
  : Lemma (requires o1 + w1 <= o2 \/ o2 + w2 <= o1)
          (ensures get (put u o2 w2 x) o1 w1 == get u o1 w1)
  = let v = put u o2 w2 x in
    put_low u o2 w2 x;
    M.pow2_plus o2 w2;
    let m = pow2 (o2 + w2) in
    let q = u / m in
    let lo = (x % pow2 w2) * pow2 o2 + u % pow2 o2 in
    assert (v == q * m + lo);
    if o1 + w1 <= o2 then begin
      // v and u agree below bit o2: the part above contributes a multiple of
      // pow2 o2, and the field itself sits at or above bit o2.
      M.paren_mul_right q (pow2 o2) (pow2 w2);
      M.swap_mul (pow2 o2) (pow2 w2);
      M.paren_mul_right q (pow2 w2) (pow2 o2);
      M.distributivity_add_left (q * pow2 w2) (x % pow2 w2) (pow2 o2);
      assert (v == u % pow2 o2 + (q * pow2 w2 + x % pow2 w2) * pow2 o2);
      M.lemma_mod_plus (u % pow2 o2) (q * pow2 w2 + x % pow2 w2) (pow2 o2);
      M.small_mod (u % pow2 o2) (pow2 o2);
      M.modulo_modulo_lemma u (pow2 o2) 1;
      bits_below v u o1 w1 o2
    end else begin
      // v and u agree above bit o2 + w2: both have quotient q there.
      M.lemma_div_plus lo q m;
      M.small_div lo m;
      M.euclidean_division_definition u m;
      M.lemma_div_plus (u % m) q m;
      M.small_div (u % m) m;
      bits_above v u o1 w1 (o2 + w2)
    end

(* The machine-width wrappers a generated module uses. The offset and width
   are always literals there, so the `o + w <= n` obligation is arithmetic on
   constants. *)

let get8 (u: U8.t) (o: nat) (w: nat { o + w <= 8 }) : x:U8.t { U8.v x == get (U8.v u) o w } =
  M.pow2_le_compat 8 w;
  U8.uint_to_t (get (U8.v u) o w)

let put8 (u: U8.t) (o: nat) (w: nat { o + w <= 8 }) (x: U8.t)
  : y:U8.t { U8.v y == put (U8.v u) o w (U8.v x) } =
  put_bound (U8.v u) o w (U8.v x) 8;
  U8.uint_to_t (put (U8.v u) o w (U8.v x))

let get16 (u: U16.t) (o: nat) (w: nat { o + w <= 16 })
  : x:U16.t { U16.v x == get (U16.v u) o w } =
  M.pow2_le_compat 16 w;
  U16.uint_to_t (get (U16.v u) o w)

let put16 (u: U16.t) (o: nat) (w: nat { o + w <= 16 }) (x: U16.t)
  : y:U16.t { U16.v y == put (U16.v u) o w (U16.v x) } =
  put_bound (U16.v u) o w (U16.v x) 16;
  U16.uint_to_t (put (U16.v u) o w (U16.v x))

let get32 (u: U32.t) (o: nat) (w: nat { o + w <= 32 })
  : x:U32.t { U32.v x == get (U32.v u) o w } =
  M.pow2_le_compat 32 w;
  U32.uint_to_t (get (U32.v u) o w)

let put32 (u: U32.t) (o: nat) (w: nat { o + w <= 32 }) (x: U32.t)
  : y:U32.t { U32.v y == put (U32.v u) o w (U32.v x) } =
  put_bound (U32.v u) o w (U32.v x) 32;
  U32.uint_to_t (put (U32.v u) o w (U32.v x))

let get64 (u: U64.t) (o: nat) (w: nat { o + w <= 64 })
  : x:U64.t { U64.v x == get (U64.v u) o w } =
  M.pow2_le_compat 64 w;
  U64.uint_to_t (get (U64.v u) o w)

let put64 (u: U64.t) (o: nat) (w: nat { o + w <= 64 }) (x: U64.t)
  : y:U64.t { U64.v y == put (U64.v u) o w (U64.v x) } =
  put_bound (U64.v u) o w (U64.v x) 64;
  U64.uint_to_t (put (U64.v u) o w (U64.v x))

(* A one-bit field whose declared type is `_Bool`: the bit is the value. *)
let getb8 (u: U8.t) (o: nat { o < 8 }) : bool = get (U8.v u) o 1 = 1
let putb8 (u: U8.t) (o: nat { o < 8 }) (x: bool) : U8.t = put8 u o 1 (if x then 1uy else 0uy)

let getb16 (u: U16.t) (o: nat { o < 16 }) : bool = get (U16.v u) o 1 = 1
let putb16 (u: U16.t) (o: nat { o < 16 }) (x: bool) : U16.t =
  put16 u o 1 (if x then 1us else 0us)

let getb32 (u: U32.t) (o: nat { o < 32 }) : bool = get (U32.v u) o 1 = 1
let putb32 (u: U32.t) (o: nat { o < 32 }) (x: bool) : U32.t =
  put32 u o 1 (if x then 1ul else 0ul)

let getb64 (u: U64.t) (o: nat { o < 64 }) : bool = get (U64.v u) o 1 = 1
let putb64 (u: U64.t) (o: nat { o < 64 }) (x: bool) : U64.t =
  put64 u o 1 (if x then 1uL else 0uL)
