module Pulse.Lib.C.Palow.Pun

(* ---------------------------------------------------------------------------
   Type punning between integer objects.

   A union member that is not the live one can still be read and written, as
   long as every byte the access covers belongs to an integer object of the
   live member: C allows it (C11 6.5.2.3p3 and footnote 95), and in Palow it
   is not a special rule but a fact about bytes. An integer's representation is
   exactly `encode n None v` -- initialised, provenance-free, and every such
   range of the right length is the representation of exactly one value. So the
   bytes under the access are the concatenation of the live member's integer
   encodings, sliced where an object only partly overlaps, and they *are* the
   encoding of the punned value.

   This module is everything that does not depend on the union: the plain-byte
   facts, a decoder for every integer type, the moves between a typed points-to
   and the raw range under it, and `overlay`, which is what a store through the
   punned name does to the bytes of the live member. PAL generates the rest per
   access -- which of the live member's objects cover the access, and the lemma
   that says so -- see `palow.md`.

   Nothing here is assumed.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow.Encoding
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes

module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64
module M = FStar.Math.Lemmas

(* Bytes an integer object could be made of. *)
let plain (b: bytes) : prop = initialized b /\ no_prov b

let plain_slice (b: bytes) (i: nat) (j: nat { i <= j /\ j <= len b })
  : Lemma (requires plain b) (ensures plain (slice b i j))
          [SMTPat (plain (slice b i j))]
  = ()

let plain_append (b1 b2: bytes)
  : Lemma (requires plain b1 /\ plain b2) (ensures plain (append b1 b2))
          [SMTPat (plain (append b1 b2))]
  = ()

let plain_encode (n: nat) (x: nat)
  : Lemma (plain (encode n None x))
          [SMTPat (plain (encode n None x))]
  = ()

(* The value a plain range encodes. `decode` is partial only on uninitialised
   bytes, so on a plain range the default is never taken. *)
let bytes_nat (b: bytes) : nat =
  match decode b with Some x -> x | None -> 0

let decode_cons (b: bytes)
  : Lemma (requires len b > 0)
          (ensures  decode b ==
                    (match (get b 0).value with
                     | None -> None
                     | Some v ->
                       (match decode (slice b 1 (len b)) with
                        | None -> None
                        | Some r -> Some (U8.v v + 256 * r))))
  = assert_norm (decode b ==
                    (if len b = 0 then Some 0 else
                     match (get b 0).value with
                     | None -> None
                     | Some v ->
                       (match decode (slice b 1 (len b)) with
                        | None -> None
                        | Some r -> Some (U8.v v + 256 * r))))

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec encode_decode (b: bytes)
  : Lemma (requires plain b)
          (ensures  bytes_nat b < pow2 (8 * len b) /\
                    b == encode (len b) None (bytes_nat b))
          (decreases (len b))
  = if len b = 0 then begin
      assert_norm (pow2 (8 * 0) == 1);
      Seq.lemma_eq_intro b (encode 0 None 0)
    end else begin
      let n = len b in
      let tl = slice b 1 n in
      encode_decode tl;
      let r = bytes_nat tl in
      decode_encode_exact (n - 1) None r;
      assert (decode tl == Some r);
      assert (Some? (get b 0).value);
      let v0 = Some?.v (get b 0).value in
      decode_cons b;
      assert (decode b == Some (U8.v v0 + 256 * r));
      let x = U8.v v0 + 256 * r in
      pow2_step n;
      assert (x < pow2 (8 * n));
      encode_head n None x;
      encode_tail n None x;
      M.lemma_mod_plus (U8.v v0) r 256;
      M.small_mod (U8.v v0) 256;
      M.lemma_div_plus (U8.v v0) r 256;
      M.small_div (U8.v v0) 256;
      let e = encode n None x in
      assert (slice e 1 n == encode (n - 1) None r);
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

(* A signed value from its two's-complement residue: `to_bits` backwards. *)
let from_bits (w: pos) (x: nat { x < pow2 w })
  : y:int { -(pow2 (w - 1)) <= y /\ y < pow2 (w - 1) }
  = M.pow2_double_sum (w - 1);
    if x >= pow2 (w - 1) then x - pow2 w else x

let to_from_bits (w: pos) (x: nat { x < pow2 w })
  : Lemma (to_bits w (from_bits w x) == x)
  = M.pow2_double_sum (w - 1)

let from_to_bits (w: pos) (x: int { -(pow2 (w - 1)) <= x /\ x < pow2 (w - 1) })
  : Lemma (from_bits w (to_bits w x) == x)
  = M.pow2_double_sum (w - 1)

(* ---------------------------------------------------------------------------
   Overlays

   `overlay old s c o` is the range `old`, which sits at offset `s`, after the
   range `c`, at offset `o`, has been written over it: each byte of `old` that
   `c` covers is replaced, the others are left alone. Offsets are absolute --
   relative to the union -- so that the same `c` and `o` can be applied to
   every object of the live member without recomputing anything, and so that
   taking a slice of an overlay is an overlay of the slice.
   --------------------------------------------------------------------------- *)

let overlay (old: bytes) (s: nat) (c: bytes) (o: nat) : r:bytes { len r == len old } =
  Seq.init (len old) (fun i -> if o <= s + i && s + i < o + len c then get c (s + i - o) else get old i)

let overlay_index (old: bytes) (s: nat) (c: bytes) (o: nat) (i: nat)
  : Lemma (requires i < len old)
          (ensures  get (overlay old s c o) i ==
                    (if o <= s + i && s + i < o + len c then get c (s + i - o) else get old i))
          [SMTPat (get (overlay old s c o) i)]
  = ()

let slice_overlay (old: bytes) (s: nat) (c: bytes) (o: nat) (i: nat) (j: nat { i <= j /\ j <= len old })
  : Lemma (slice (overlay old s c o) i j == overlay (slice old i j) (s + i) c o)
          [SMTPat (slice (overlay old s c o) i j)]
  = Seq.lemma_eq_intro (slice (overlay old s c o) i j) (overlay (slice old i j) (s + i) c o)

let overlay_disjoint (old: bytes) (s: nat) (c: bytes) (o: nat)
  : Lemma (requires s + len old <= o \/ o + len c <= s)
          (ensures  overlay old s c o == old)
          [SMTPat (overlay old s c o)]
  = Seq.lemma_eq_intro (overlay old s c o) old

let overlay_plain (old: bytes) (s: nat) (c: bytes) (o: nat)
  : Lemma (requires plain old /\ plain c)
          (ensures  plain (overlay old s c o))
          [SMTPat (plain (overlay old s c o))]
  = ()

(* A range written exactly over a leaf replaces it. *)
let overlay_exact (old: bytes) (s: nat) (c: bytes)
  : Lemma (requires len c == len old)
          (ensures  overlay old s c s == c)
          [SMTPat (overlay old s c s)]
  = Seq.lemma_eq_intro (overlay old s c s) c

(* Writing a range back over itself changes nothing. *)
let overlay_self (b: bytes) (o: nat) (n: nat { o + n <= len b })
  : Lemma (overlay b 0 (slice b o (o + n)) o == b)
  = Seq.lemma_eq_intro (overlay b 0 (slice b o (o + n)) o) b

(* ---------------------------------------------------------------------------
   Carving a window out of a range, and putting it back
   --------------------------------------------------------------------------- *)

let carve_rest (a: ptr) (p: perm) (b: bytes) (o: SZ.t)
               (n: SZ.t { SZ.v o + SZ.v n <= len b /\ SZ.fits (SZ.v o + SZ.v n) }) : slprop =
  mem_pts_to a p (slice b 0 (SZ.v o)) **
  mem_pts_to (a +! SZ.add o n) p (slice b (SZ.v o + SZ.v n) (len b))

ghost fn mem_carve (a: ptr) (#p: perm) (#b: bytes) (o: SZ.t)
                   (n: SZ.t { SZ.v o + SZ.v n <= len b /\ SZ.fits (SZ.v o + SZ.v n) })
  requires mem_pts_to a p b
  ensures  mem_pts_to (a +! o) p (slice b (SZ.v o) (SZ.v o + SZ.v n))
  ensures  carve_rest a p b o n
{
  mem_split a o;
  mem_split (a +! o) n;
  Seq.slice_slice b (SZ.v o) (len b) 0 (SZ.v n);
  Seq.slice_slice b (SZ.v o) (len b) (SZ.v n) (len b - SZ.v o);
  rewrite (mem_pts_to (a +! o) p (slice (slice b (SZ.v o) (len b)) 0 (SZ.v n)))
       as (mem_pts_to (a +! o) p (slice b (SZ.v o) (SZ.v o + SZ.v n)));
  rewrite (mem_pts_to ((a +! o) +! n) p
             (slice (slice b (SZ.v o) (len b)) (SZ.v n) (len (slice b (SZ.v o) (len b)))))
       as (mem_pts_to (a +! SZ.add o n) p (slice b (SZ.v o + SZ.v n) (len b)));
  fold (carve_rest a p b o n);
}

ghost fn mem_uncarve (a: ptr) (#p: perm) (#b: bytes) (o: SZ.t)
                     (n: SZ.t { SZ.v o + SZ.v n <= len b /\ SZ.fits (SZ.v o + SZ.v n) })
                     (#c: bytes { len c == SZ.v n })
  requires mem_pts_to (a +! o) p c
  requires carve_rest a p b o n
  ensures  mem_pts_to a p (overlay b 0 c (SZ.v o))
{
  unfold (carve_rest a p b o n);
  rewrite (mem_pts_to (a +! SZ.add o n) p (slice b (SZ.v o + SZ.v n) (len b)))
       as (mem_pts_to ((a +! o) +! n) p (slice b (SZ.v o + SZ.v n) (len b)));
  mem_join (a +! o) #p #c #(slice b (SZ.v o + SZ.v n) (len b)) n;
  mem_join a #p #(slice b 0 (SZ.v o)) o;
  let r = Ghost.hide (append (slice b 0 (SZ.v o)) (append c (slice b (SZ.v o + SZ.v n) (len b))));
  Seq.lemma_eq_intro r (overlay b 0 c (SZ.v o));
  rewrite (mem_pts_to a p (append (slice b 0 (SZ.v o)) (append c (slice b (SZ.v o + SZ.v n) (len b)))))
       as (mem_pts_to a p (overlay b 0 c (SZ.v o)));
}

(* ---------------------------------------------------------------------------
   Per integer type: its bytes, the value of a plain range, and the moves
   between the typed points-to and the range under it.
   --------------------------------------------------------------------------- *)

(* uint8_t *)
let uint8_t_bytes (x: U8.t) : bytes = encode 1 None (U8.v x)

let uint8_t_of_bytes (b: bytes) : U8.t = U8.uint_to_t (bytes_nat b % pow2 8)

let uint8_t_bytes_repr (x: U8.t)
  : Lemma (uint8_t_repr x (uint8_t_bytes x) /\ len (uint8_t_bytes x) == 1 /\ plain (uint8_t_bytes x))
          [SMTPat (uint8_t_bytes x)]
  = ()

let uint8_t_of_bytes_bytes (x: U8.t)
  : Lemma (uint8_t_of_bytes (uint8_t_bytes x) == x)
          [SMTPat (uint8_t_of_bytes (uint8_t_bytes x))]
  = decode_encode_exact 1 None (U8.v x);
    M.small_mod (U8.v x) (pow2 8)

let uint8_t_bytes_of_bytes (b: bytes)
  : Lemma (requires plain b /\ len b == 1)
          (ensures  uint8_t_bytes (uint8_t_of_bytes b) == b)
          [SMTPat (uint8_t_bytes (uint8_t_of_bytes b))]
  = encode_decode b;
    M.small_mod (bytes_nat b) (pow2 8)

ghost fn uint8_t_of_mem (a: ptr) (#p: perm) (#b: bytes)
  requires mem_pts_to a p b
  requires pure (plain b /\ len b == 1 /\ aligned a uint8_t_alignof)
  ensures  uint8_t_pts_to a p (uint8_t_of_bytes b)
{
  uint8_t_bytes_of_bytes b;
  uint8_t_conceal a #p #b #(uint8_t_of_bytes b);
}

ghost fn uint8_t_to_mem (a: ptr) (#p: perm) (#x: U8.t)
  requires uint8_t_pts_to a p x
  ensures  mem_pts_to a p (uint8_t_bytes x)
{
  uint8_t_reveal a;
  with b. assert (mem_pts_to a p b);
  rewrite (mem_pts_to a p b) as (mem_pts_to a p (uint8_t_bytes x));
}

(* uint16_t *)
let uint16_t_bytes (x: U16.t) : bytes = encode 2 None (U16.v x)

let uint16_t_of_bytes (b: bytes) : U16.t = U16.uint_to_t (bytes_nat b % pow2 16)

let uint16_t_bytes_repr (x: U16.t)
  : Lemma (uint16_t_repr x (uint16_t_bytes x) /\ len (uint16_t_bytes x) == 2 /\ plain (uint16_t_bytes x))
          [SMTPat (uint16_t_bytes x)]
  = ()

let uint16_t_of_bytes_bytes (x: U16.t)
  : Lemma (uint16_t_of_bytes (uint16_t_bytes x) == x)
          [SMTPat (uint16_t_of_bytes (uint16_t_bytes x))]
  = decode_encode_exact 2 None (U16.v x);
    M.small_mod (U16.v x) (pow2 16)

let uint16_t_bytes_of_bytes (b: bytes)
  : Lemma (requires plain b /\ len b == 2)
          (ensures  uint16_t_bytes (uint16_t_of_bytes b) == b)
          [SMTPat (uint16_t_bytes (uint16_t_of_bytes b))]
  = encode_decode b;
    M.small_mod (bytes_nat b) (pow2 16)

ghost fn uint16_t_of_mem (a: ptr) (#p: perm) (#b: bytes)
  requires mem_pts_to a p b
  requires pure (plain b /\ len b == 2 /\ aligned a uint16_t_alignof)
  ensures  uint16_t_pts_to a p (uint16_t_of_bytes b)
{
  uint16_t_bytes_of_bytes b;
  uint16_t_conceal a #p #b #(uint16_t_of_bytes b);
}

ghost fn uint16_t_to_mem (a: ptr) (#p: perm) (#x: U16.t)
  requires uint16_t_pts_to a p x
  ensures  mem_pts_to a p (uint16_t_bytes x)
{
  uint16_t_reveal a;
  with b. assert (mem_pts_to a p b);
  rewrite (mem_pts_to a p b) as (mem_pts_to a p (uint16_t_bytes x));
}

(* uint32_t *)
let uint32_t_bytes (x: U32.t) : bytes = encode 4 None (U32.v x)

let uint32_t_of_bytes (b: bytes) : U32.t = U32.uint_to_t (bytes_nat b % pow2 32)

let uint32_t_bytes_repr (x: U32.t)
  : Lemma (uint32_t_repr x (uint32_t_bytes x) /\ len (uint32_t_bytes x) == 4 /\ plain (uint32_t_bytes x))
          [SMTPat (uint32_t_bytes x)]
  = ()

let uint32_t_of_bytes_bytes (x: U32.t)
  : Lemma (uint32_t_of_bytes (uint32_t_bytes x) == x)
          [SMTPat (uint32_t_of_bytes (uint32_t_bytes x))]
  = decode_encode_exact 4 None (U32.v x);
    M.small_mod (U32.v x) (pow2 32)

let uint32_t_bytes_of_bytes (b: bytes)
  : Lemma (requires plain b /\ len b == 4)
          (ensures  uint32_t_bytes (uint32_t_of_bytes b) == b)
          [SMTPat (uint32_t_bytes (uint32_t_of_bytes b))]
  = encode_decode b;
    M.small_mod (bytes_nat b) (pow2 32)

ghost fn uint32_t_of_mem (a: ptr) (#p: perm) (#b: bytes)
  requires mem_pts_to a p b
  requires pure (plain b /\ len b == 4 /\ aligned a uint32_t_alignof)
  ensures  uint32_t_pts_to a p (uint32_t_of_bytes b)
{
  uint32_t_bytes_of_bytes b;
  uint32_t_conceal a #p #b #(uint32_t_of_bytes b);
}

ghost fn uint32_t_to_mem (a: ptr) (#p: perm) (#x: U32.t)
  requires uint32_t_pts_to a p x
  ensures  mem_pts_to a p (uint32_t_bytes x)
{
  uint32_t_reveal a;
  with b. assert (mem_pts_to a p b);
  rewrite (mem_pts_to a p b) as (mem_pts_to a p (uint32_t_bytes x));
}

(* uint64_t *)
let uint64_t_bytes (x: U64.t) : bytes = encode 8 None (U64.v x)

let uint64_t_of_bytes (b: bytes) : U64.t = U64.uint_to_t (bytes_nat b % pow2 64)

let uint64_t_bytes_repr (x: U64.t)
  : Lemma (uint64_t_repr x (uint64_t_bytes x) /\ len (uint64_t_bytes x) == 8 /\ plain (uint64_t_bytes x))
          [SMTPat (uint64_t_bytes x)]
  = ()

let uint64_t_of_bytes_bytes (x: U64.t)
  : Lemma (uint64_t_of_bytes (uint64_t_bytes x) == x)
          [SMTPat (uint64_t_of_bytes (uint64_t_bytes x))]
  = decode_encode_exact 8 None (U64.v x);
    M.small_mod (U64.v x) (pow2 64)

let uint64_t_bytes_of_bytes (b: bytes)
  : Lemma (requires plain b /\ len b == 8)
          (ensures  uint64_t_bytes (uint64_t_of_bytes b) == b)
          [SMTPat (uint64_t_bytes (uint64_t_of_bytes b))]
  = encode_decode b;
    M.small_mod (bytes_nat b) (pow2 64)

ghost fn uint64_t_of_mem (a: ptr) (#p: perm) (#b: bytes)
  requires mem_pts_to a p b
  requires pure (plain b /\ len b == 8 /\ aligned a uint64_t_alignof)
  ensures  uint64_t_pts_to a p (uint64_t_of_bytes b)
{
  uint64_t_bytes_of_bytes b;
  uint64_t_conceal a #p #b #(uint64_t_of_bytes b);
}

ghost fn uint64_t_to_mem (a: ptr) (#p: perm) (#x: U64.t)
  requires uint64_t_pts_to a p x
  ensures  mem_pts_to a p (uint64_t_bytes x)
{
  uint64_t_reveal a;
  with b. assert (mem_pts_to a p b);
  rewrite (mem_pts_to a p b) as (mem_pts_to a p (uint64_t_bytes x));
}

(* int8_t *)
let int8_t_bytes (x: I8.t) : bytes = encode 1 None (to_bits 8 (I8.v x))

let int8_t_of_bytes (b: bytes) : I8.t = I8.int_to_t (from_bits 8 (bytes_nat b % pow2 8))

let int8_t_bytes_repr (x: I8.t)
  : Lemma (int8_t_repr x (int8_t_bytes x) /\ len (int8_t_bytes x) == 1 /\ plain (int8_t_bytes x))
          [SMTPat (int8_t_bytes x)]
  = ()

let int8_t_of_bytes_bytes (x: I8.t)
  : Lemma (int8_t_of_bytes (int8_t_bytes x) == x)
          [SMTPat (int8_t_of_bytes (int8_t_bytes x))]
  = decode_encode_exact 1 None (to_bits 8 (I8.v x));
    M.small_mod (to_bits 8 (I8.v x)) (pow2 8); from_to_bits 8 (I8.v x)

let int8_t_bytes_of_bytes (b: bytes)
  : Lemma (requires plain b /\ len b == 1)
          (ensures  int8_t_bytes (int8_t_of_bytes b) == b)
          [SMTPat (int8_t_bytes (int8_t_of_bytes b))]
  = encode_decode b;
    M.small_mod (bytes_nat b) (pow2 8);
    to_from_bits 8 (bytes_nat b % pow2 8)

ghost fn int8_t_of_mem (a: ptr) (#p: perm) (#b: bytes)
  requires mem_pts_to a p b
  requires pure (plain b /\ len b == 1 /\ aligned a int8_t_alignof)
  ensures  int8_t_pts_to a p (int8_t_of_bytes b)
{
  int8_t_bytes_of_bytes b;
  int8_t_conceal a #p #b #(int8_t_of_bytes b);
}

ghost fn int8_t_to_mem (a: ptr) (#p: perm) (#x: I8.t)
  requires int8_t_pts_to a p x
  ensures  mem_pts_to a p (int8_t_bytes x)
{
  int8_t_reveal a;
  with b. assert (mem_pts_to a p b);
  rewrite (mem_pts_to a p b) as (mem_pts_to a p (int8_t_bytes x));
}

(* int16_t *)
let int16_t_bytes (x: I16.t) : bytes = encode 2 None (to_bits 16 (I16.v x))

let int16_t_of_bytes (b: bytes) : I16.t = I16.int_to_t (from_bits 16 (bytes_nat b % pow2 16))

let int16_t_bytes_repr (x: I16.t)
  : Lemma (int16_t_repr x (int16_t_bytes x) /\ len (int16_t_bytes x) == 2 /\ plain (int16_t_bytes x))
          [SMTPat (int16_t_bytes x)]
  = ()

let int16_t_of_bytes_bytes (x: I16.t)
  : Lemma (int16_t_of_bytes (int16_t_bytes x) == x)
          [SMTPat (int16_t_of_bytes (int16_t_bytes x))]
  = decode_encode_exact 2 None (to_bits 16 (I16.v x));
    M.small_mod (to_bits 16 (I16.v x)) (pow2 16); from_to_bits 16 (I16.v x)

let int16_t_bytes_of_bytes (b: bytes)
  : Lemma (requires plain b /\ len b == 2)
          (ensures  int16_t_bytes (int16_t_of_bytes b) == b)
          [SMTPat (int16_t_bytes (int16_t_of_bytes b))]
  = encode_decode b;
    M.small_mod (bytes_nat b) (pow2 16);
    to_from_bits 16 (bytes_nat b % pow2 16)

ghost fn int16_t_of_mem (a: ptr) (#p: perm) (#b: bytes)
  requires mem_pts_to a p b
  requires pure (plain b /\ len b == 2 /\ aligned a int16_t_alignof)
  ensures  int16_t_pts_to a p (int16_t_of_bytes b)
{
  int16_t_bytes_of_bytes b;
  int16_t_conceal a #p #b #(int16_t_of_bytes b);
}

ghost fn int16_t_to_mem (a: ptr) (#p: perm) (#x: I16.t)
  requires int16_t_pts_to a p x
  ensures  mem_pts_to a p (int16_t_bytes x)
{
  int16_t_reveal a;
  with b. assert (mem_pts_to a p b);
  rewrite (mem_pts_to a p b) as (mem_pts_to a p (int16_t_bytes x));
}

(* int32_t *)
let int32_t_bytes (x: I32.t) : bytes = encode 4 None (to_bits 32 (I32.v x))

let int32_t_of_bytes (b: bytes) : I32.t = I32.int_to_t (from_bits 32 (bytes_nat b % pow2 32))

let int32_t_bytes_repr (x: I32.t)
  : Lemma (int32_t_repr x (int32_t_bytes x) /\ len (int32_t_bytes x) == 4 /\ plain (int32_t_bytes x))
          [SMTPat (int32_t_bytes x)]
  = ()

let int32_t_of_bytes_bytes (x: I32.t)
  : Lemma (int32_t_of_bytes (int32_t_bytes x) == x)
          [SMTPat (int32_t_of_bytes (int32_t_bytes x))]
  = decode_encode_exact 4 None (to_bits 32 (I32.v x));
    M.small_mod (to_bits 32 (I32.v x)) (pow2 32); from_to_bits 32 (I32.v x)

let int32_t_bytes_of_bytes (b: bytes)
  : Lemma (requires plain b /\ len b == 4)
          (ensures  int32_t_bytes (int32_t_of_bytes b) == b)
          [SMTPat (int32_t_bytes (int32_t_of_bytes b))]
  = encode_decode b;
    M.small_mod (bytes_nat b) (pow2 32);
    to_from_bits 32 (bytes_nat b % pow2 32)

ghost fn int32_t_of_mem (a: ptr) (#p: perm) (#b: bytes)
  requires mem_pts_to a p b
  requires pure (plain b /\ len b == 4 /\ aligned a int32_t_alignof)
  ensures  int32_t_pts_to a p (int32_t_of_bytes b)
{
  int32_t_bytes_of_bytes b;
  int32_t_conceal a #p #b #(int32_t_of_bytes b);
}

ghost fn int32_t_to_mem (a: ptr) (#p: perm) (#x: I32.t)
  requires int32_t_pts_to a p x
  ensures  mem_pts_to a p (int32_t_bytes x)
{
  int32_t_reveal a;
  with b. assert (mem_pts_to a p b);
  rewrite (mem_pts_to a p b) as (mem_pts_to a p (int32_t_bytes x));
}

(* int64_t *)
let int64_t_bytes (x: I64.t) : bytes = encode 8 None (to_bits 64 (I64.v x))

let int64_t_of_bytes (b: bytes) : I64.t = I64.int_to_t (from_bits 64 (bytes_nat b % pow2 64))

let int64_t_bytes_repr (x: I64.t)
  : Lemma (int64_t_repr x (int64_t_bytes x) /\ len (int64_t_bytes x) == 8 /\ plain (int64_t_bytes x))
          [SMTPat (int64_t_bytes x)]
  = ()

let int64_t_of_bytes_bytes (x: I64.t)
  : Lemma (int64_t_of_bytes (int64_t_bytes x) == x)
          [SMTPat (int64_t_of_bytes (int64_t_bytes x))]
  = decode_encode_exact 8 None (to_bits 64 (I64.v x));
    M.small_mod (to_bits 64 (I64.v x)) (pow2 64); from_to_bits 64 (I64.v x)

let int64_t_bytes_of_bytes (b: bytes)
  : Lemma (requires plain b /\ len b == 8)
          (ensures  int64_t_bytes (int64_t_of_bytes b) == b)
          [SMTPat (int64_t_bytes (int64_t_of_bytes b))]
  = encode_decode b;
    M.small_mod (bytes_nat b) (pow2 64);
    to_from_bits 64 (bytes_nat b % pow2 64)

ghost fn int64_t_of_mem (a: ptr) (#p: perm) (#b: bytes)
  requires mem_pts_to a p b
  requires pure (plain b /\ len b == 8 /\ aligned a int64_t_alignof)
  ensures  int64_t_pts_to a p (int64_t_of_bytes b)
{
  int64_t_bytes_of_bytes b;
  int64_t_conceal a #p #b #(int64_t_of_bytes b);
}

ghost fn int64_t_to_mem (a: ptr) (#p: perm) (#x: I64.t)
  requires int64_t_pts_to a p x
  ensures  mem_pts_to a p (int64_t_bytes x)
{
  int64_t_reveal a;
  with b. assert (mem_pts_to a p b);
  rewrite (mem_pts_to a p b) as (mem_pts_to a p (int64_t_bytes x));
}

(* size_t *)
let size_t_bytes (x: SZ.t) : bytes = encode 8 None (SZ.v x)

let size_t_of_bytes (b: bytes) : SZ.t = sizet_of_uint64 (U64.uint_to_t (bytes_nat b % pow2 64))

let size_t_bytes_repr (x: SZ.t)
  : Lemma (size_t_repr x (size_t_bytes x) /\ len (size_t_bytes x) == 8 /\ plain (size_t_bytes x))
          [SMTPat (size_t_bytes x)]
  = ()

let size_t_of_bytes_bytes (x: SZ.t)
  : Lemma (size_t_of_bytes (size_t_bytes x) == x)
          [SMTPat (size_t_of_bytes (size_t_bytes x))]
  = decode_encode_exact 8 None (SZ.v x);
    M.small_mod (SZ.v x) (pow2 64)

let size_t_bytes_of_bytes (b: bytes)
  : Lemma (requires plain b /\ len b == 8)
          (ensures  size_t_bytes (size_t_of_bytes b) == b)
          [SMTPat (size_t_bytes (size_t_of_bytes b))]
  = encode_decode b;
    M.small_mod (bytes_nat b) (pow2 64)

ghost fn size_t_of_mem (a: ptr) (#p: perm) (#b: bytes)
  requires mem_pts_to a p b
  requires pure (plain b /\ len b == 8 /\ aligned a size_t_alignof)
  ensures  size_t_pts_to a p (size_t_of_bytes b)
{
  size_t_bytes_of_bytes b;
  size_t_conceal a #p #b #(size_t_of_bytes b);
}

ghost fn size_t_to_mem (a: ptr) (#p: perm) (#x: SZ.t)
  requires size_t_pts_to a p x
  ensures  mem_pts_to a p (size_t_bytes x)
{
  size_t_reveal a;
  with b. assert (mem_pts_to a p b);
  rewrite (mem_pts_to a p b) as (mem_pts_to a p (size_t_bytes x));
}
