module Pulse.Lib.C.Palow.RawBytes

(* ---------------------------------------------------------------------------
   Character access to raw storage.

   C lets any object be accessed through a character lvalue (C11 6.5p7), and a
   character store installs no effective type (6.5p6). So a byte read or a byte
   write needs no typed ownership at all: it is an operation on the bytes and
   their index, and it leaves the index alone. Both are derived here from the
   indexed machine's `load` and `store` at `unsigned char`, which the index
   always licenses.

   The other half is the way back: once a range of bytes has been written one
   character at a time, a typed read of it needs a value those bytes are the
   representation of. For an unsigned integer type every initialised,
   provenance-free range of the right width is one, and `decode` names it.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Encoding
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes

module ET = Pulse.Lib.C.Palow.Etype
module EM = Pulse.Lib.C.Palow.Effective.Machine
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

(* What a character store of `y` leaves in the byte it writes. *)
let byte_of (y: U8.t) : byte = { value = Some y; prov = None }

(* Bytes an integer could have been stored as: every one written, none
   carrying a pointer's provenance. *)
(* Total so that a contract can mention it before its bound is established. *)
let upd_byte (b: bytes) (i: nat) (y: U8.t) : bytes =
  if i < len b then Seq.upd b i (byte_of y) else b

let value_of (b: bytes) (i: nat) : option U8.t =
  if i < len b then (get b i).value else None

let defined (b: bytes) : prop = initialized b /\ no_prov b

let defined_upd (b: bytes) (i: nat) (y: U8.t)
  : Lemma (requires defined b)
          (ensures defined (upd_byte b i y))
          [SMTPat (defined (upd_byte b i y))]
  = ()

let defined_slice (b: bytes) (i: nat) (j: nat { i <= j /\ j <= len b })
  : Lemma (requires defined b)
          (ensures defined (slice b i j))
          [SMTPat (defined (slice b i j))]
  = ()

let zeroed_defined (n: nat)
  : Lemma (defined (zeroed n))
          [SMTPat (defined (zeroed n))]
  = ()

let upd_len (b: bytes) (i: nat) (y: U8.t)
  : Lemma (len (upd_byte b i y) == len b)
          [SMTPat (len (upd_byte b i y))]
  = ()

let upd_value (b: bytes) (i: nat) (y: U8.t) (k: nat)
  : Lemma (value_of (upd_byte b i y) k ==
           (if k = i && i < len b then Some y else value_of b k))
          [SMTPat (value_of (upd_byte b i y) k)]
  = ()

(* ---------------------------------------------------------------------------
   Decoding
   --------------------------------------------------------------------------- *)

let decode_nat (b: bytes) : nat =
  match decode b with Some x -> x | None -> 0

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec decode_complete (b: bytes)
  : Lemma (requires defined b)
          (ensures Some? (decode b) /\ decode_nat b < pow2 (8 * len b) /\
                   encode (len b) None (decode_nat b) == b)
          (decreases (len b))
  = if len b = 0 then begin
      assert_norm (pow2 (8 * 0) == 1);
      Seq.lemma_eq_intro (encode 0 None 0) b
    end else begin
      let n = len b in
      let t = slice b 1 n in
      decode_complete t;
      let r = decode_nat t in
      let v = Some?.v (get b 0).value in
      let x = U8.v v + 256 * r in
      assert (decode b == Some x);
      pow2_step n;
      M.lemma_mod_plus (U8.v v) r 256;
      M.small_mod (U8.v v) 256;
      M.lemma_div_plus (U8.v v) r 256;
      M.small_div (U8.v v) 256;
      encode_head n None x;
      encode_tail n None x;
      let e = encode n None x in
      let aux (i: nat { i < n }) : Lemma (get e i == get b i) =
        if i > 0 then begin
          let j : nat = i - 1 in
          Seq.lemma_index_slice e 1 n j;
          Seq.lemma_index_slice b 1 n j
        end
      in
      Classical.forall_intro aux;
      bytes_ext e b
    end
#pop-options

let uint8_t_of_bytes (b: bytes) : U8.t =
  if decode_nat b < pow2 8 then U8.uint_to_t (decode_nat b) else 0uy

let uint8_t_decode (b: bytes)
  : Lemma (requires len b == 1 /\ defined b)
          (ensures uint8_t_repr (uint8_t_of_bytes b) b)
  = decode_complete b

let uint16_t_of_bytes (b: bytes) : U16.t =
  if decode_nat b < pow2 16 then U16.uint_to_t (decode_nat b) else 0us

let uint16_t_decode (b: bytes)
  : Lemma (requires len b == 2 /\ defined b)
          (ensures uint16_t_repr (uint16_t_of_bytes b) b)
  = decode_complete b

let uint32_t_of_bytes (b: bytes) : U32.t =
  if decode_nat b < pow2 32 then U32.uint_to_t (decode_nat b) else 0ul

let uint32_t_decode (b: bytes)
  : Lemma (requires len b == 4 /\ defined b)
          (ensures uint32_t_repr (uint32_t_of_bytes b) b)
  = decode_complete b

let uint64_t_of_bytes (b: bytes) : U64.t =
  if decode_nat b < pow2 64 then U64.uint_to_t (decode_nat b) else 0uL

let uint64_t_decode (b: bytes)
  : Lemma (requires len b == 8 /\ defined b)
          (ensures uint64_t_repr (uint64_t_of_bytes b) b)
  = decode_complete b

let ulong_long_t_of_bytes (b: bytes) : U64.t = uint64_t_of_bytes b

let ulong_long_t_decode (b: bytes)
  : Lemma (requires len b == 8 /\ defined b)
          (ensures ulong_long_t_repr (ulong_long_t_of_bytes b) b)
  = decode_complete b

(* A signed integer is encoded as its two's-complement residue (`to_bits`), so
   decoding one is the inverse map on residues. *)
let of_bits (w: pos) (n: nat { n < pow2 w })
  : x:int { -(pow2 (w - 1)) <= x /\ x < pow2 (w - 1) /\ to_bits w x == n }
  = M.pow2_double_sum (w - 1);
    if n < pow2 (w - 1) then n else n - pow2 w

let int8_t_of_bytes (b: bytes) : I8.t =
  if decode_nat b < pow2 8 then I8.int_to_t (of_bits 8 (decode_nat b)) else 0y

let int8_t_decode (b: bytes)
  : Lemma (requires len b == 1 /\ defined b)
          (ensures int8_t_repr (int8_t_of_bytes b) b)
  = decode_complete b

let int16_t_of_bytes (b: bytes) : I16.t =
  if decode_nat b < pow2 16 then I16.int_to_t (of_bits 16 (decode_nat b)) else 0s

let int16_t_decode (b: bytes)
  : Lemma (requires len b == 2 /\ defined b)
          (ensures int16_t_repr (int16_t_of_bytes b) b)
  = decode_complete b

let int32_t_of_bytes (b: bytes) : I32.t =
  if decode_nat b < pow2 32 then I32.int_to_t (of_bits 32 (decode_nat b)) else 0l

let int32_t_decode (b: bytes)
  : Lemma (requires len b == 4 /\ defined b)
          (ensures int32_t_repr (int32_t_of_bytes b) b)
  = decode_complete b

let int64_t_of_bytes (b: bytes) : I64.t =
  if decode_nat b < pow2 64 then I64.int_to_t (of_bits 64 (decode_nat b)) else 0L

let int64_t_decode (b: bytes)
  : Lemma (requires len b == 8 /\ defined b)
          (ensures int64_t_repr (int64_t_of_bytes b) b)
  = decode_complete b

let long_long_t_of_bytes (b: bytes) : I64.t = int64_t_of_bytes b

let long_long_t_decode (b: bytes)
  : Lemma (requires len b == 8 /\ defined b)
          (ensures long_long_t_repr (long_long_t_of_bytes b) b)
  = decode_complete b

(* `_Bool` has one value bit (6.2.5p2, 6.2.6.2p1), and every target PAL
   supports gives the other bits no meaning: a byte other than 0 or 1 is not a
   `_Bool` value, and reading one is undefined (6.2.6.1p5). Hence the extra
   precondition, which is what a pun into a `_Bool` has to establish. *)
let bool_t_valid (b: bytes) : prop = defined b /\ decode_nat b <= 1

let bool_t_of_bytes (b: bytes) : bool = decode_nat b = 1

let bool_t_decode (b: bytes)
  : Lemma (requires len b == 1 /\ bool_t_valid b)
          (ensures bool_t_repr (bool_t_of_bytes b) b)
  = decode_complete b

(* ---------------------------------------------------------------------------
   Byte access
   --------------------------------------------------------------------------- *)

let store_one_index (e: ET.etypes) (i: nat)
  : Lemma (requires i < ET.elen e)
          (ensures Seq.append (Seq.slice e 0 i)
                     (Seq.append (EM.store_index (Seq.slice e i (i + 1)) uint8_t_ctype)
                                 (Seq.slice e (i + 1) (ET.elen e))) == e)
  = Seq.lemma_eq_intro
      (Seq.append (Seq.slice e 0 i)
        (Seq.append (Seq.slice e i (i + 1)) (Seq.slice e (i + 1) (ET.elen e)))) e

let store_one_bytes (b: bytes) (i: nat { i < len b }) (y: U8.t)
  : Lemma (append (slice b 0 i)
             (append (encode 1 None (U8.v y)) (slice b (i + 1) (len b)))
           == upd_byte b i y)
  = let l = append (slice b 0 i)
              (append (encode 1 None (U8.v y)) (slice b (i + 1) (len b))) in
    assert_norm (pow2 (8 * 0) == 1);
    let aux (k: nat { k < len b }) : Lemma (get l k == get (Seq.upd b i (byte_of y)) k) =
      if k = i then encode_index 1 None (U8.v y) 0 else ()
    in
    Classical.forall_intro aux;
    bytes_ext l (Seq.upd b i (byte_of y))

let value_at (b: bytes) (i: nat { i < len b /\ Some? (get b i).value }) : U8.t =
  Some?.v (get b i).value

let load_one_bytes (b: bytes) (i: nat { i < len b })
  : Lemma (append (slice b 0 i) (append (slice b i (i + 1)) (slice b (i + 1) (len b))) == b)
  = Seq.lemma_eq_intro
      (append (slice b 0 i) (append (slice b i (i + 1)) (slice b (i + 1) (len b)))) b

let byte_read_ok (e: ET.etypes) (i: nat)
  : Lemma (requires ET.etypes_wf e /\ i < ET.elen e)
          (ensures ET.read_ok (Seq.slice (Seq.slice e i (ET.elen e)) 0 1) uint8_t_ctype)
  = let s = Seq.slice (Seq.slice e i (ET.elen e)) 0 1 in
    assert (ET.eget s 0 == ET.eget e i);
    ET.read_char_ok s

let none_wf (n: nat)
  : Lemma (ET.etypes_wf (Seq.create n None))
          [SMTPat (ET.etypes_wf (Seq.create n None))]
  = ()

(* Bytes some type may read belong to objects they fit inside. *)
let read_ok_wf (e: ET.etypes) (t: ET.ctype)
  : Lemma (requires ET.read_ok e t)
          (ensures ET.etypes_wf e)
  = ()

let initialized_value (b: bytes) (i: nat)
  : Lemma (requires initialized b /\ i < len b)
          (ensures Some? (value_of b i))
  = ()

let fresh_wf (n: nat)
  : Lemma (ET.etypes_wf (EM.fresh_index n))
          [SMTPat (ET.etypes_wf (EM.fresh_index n))]
  = ()

(* A character store: `b[i] = y` for `unsigned char *b = a`. *)
fn byte_store (a: ptr) (i: SZ.t) (y: U8.t) (#b: erased bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (SZ.v i < len b /\ ET.elen e == len b /\ ET.etypes_wf e)
  ensures mem_pts_to_at a 1.0R (upd_byte b (SZ.v i) y) e
{
  byte_read_ok e (SZ.v i);
  mem_split_at a i;
  mem_split_at (a +! i) 1sz;
  encode_has_prov 1 None (U8.v y);
  EM.store (a +! i) (hide uint8_t_ctype) (encode 1 None (U8.v y));
  mem_join_at (a +! i) 1sz;
  mem_join_at a i;
  store_one_bytes b (SZ.v i) y;
  store_one_index e (SZ.v i);
  rewrite each
    (append (slice b 0 (SZ.v i))
       (append (encode 1 None (U8.v y)) (slice (slice b (SZ.v i) (len b)) 1 (len (slice b (SZ.v i) (len b))))))
    as (upd_byte b (SZ.v i) y);
  rewrite each
    (Seq.append (Seq.slice e 0 (SZ.v i))
       (Seq.append (EM.store_index (Seq.slice (Seq.slice e (SZ.v i) (ET.elen e)) 0 1) uint8_t_ctype)
                   (Seq.slice (Seq.slice e (SZ.v i) (ET.elen e)) 1 (ET.elen (Seq.slice e (SZ.v i) (ET.elen e))))))
    as e;
}

(* A character load: `b[i]` for `unsigned char *b = a`. *)
fn byte_load (a: ptr) (i: SZ.t) (#p: perm) (#b: erased bytes) (#e: ET.etypes)
  preserves mem_pts_to_at a p b e
  requires pure (SZ.v i < len b /\ ET.elen e == len b /\ ET.etypes_wf e /\
                 Some? (value_of b (SZ.v i)))
  returns y: U8.t
  ensures pure (value_of b (SZ.v i) == Some y)
{
  byte_read_ok e (SZ.v i);
  mem_split_at a i;
  mem_split_at (a +! i) 1sz;
  let r = EM.load (a +! i) (hide uint8_t_ctype);
  let y = value_at r 0;
  mem_join_at (a +! i) 1sz;
  mem_join_at a i;
  load_one_bytes b (SZ.v i);
  Seq.lemma_eq_intro
    (Seq.append (Seq.slice e 0 (SZ.v i))
       (Seq.append (Seq.slice (Seq.slice e (SZ.v i) (ET.elen e)) 0 1)
                   (Seq.slice (Seq.slice e (SZ.v i) (ET.elen e)) 1 (ET.elen (Seq.slice e (SZ.v i) (ET.elen e))))))
    e;
  Seq.lemma_eq_intro
    (append (slice b 0 (SZ.v i))
       (append (slice (slice b (SZ.v i) (len b)) 0 1)
               (slice (slice b (SZ.v i) (len b)) 1 (len (slice b (SZ.v i) (len b))))))
    b;
  rewrite each
    (append (slice b 0 (SZ.v i))
       (append (slice (slice b (SZ.v i) (len b)) 0 1)
               (slice (slice b (SZ.v i) (len b)) 1 (len (slice b (SZ.v i) (len b))))))
    as (reveal b);
  rewrite each
    (Seq.append (Seq.slice e 0 (SZ.v i))
       (Seq.append (Seq.slice (Seq.slice e (SZ.v i) (ET.elen e)) 0 1)
                   (Seq.slice (Seq.slice e (SZ.v i) (ET.elen e)) 1 (ET.elen (Seq.slice e (SZ.v i) (ET.elen e))))))
    as e;
  y
}
