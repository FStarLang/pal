module Pulse.Lib.C.Palow.Overlay

(* ---------------------------------------------------------------------------
   Overlay unions.

   A union marked `_overlay` is not a choice between its members: it is one
   object that every member is a view of, the way a request is laid out when
   several layers each own their own fields of it. Its value is its bytes, so
   a store through any member changes exactly the bytes that member's field
   occupies and every other byte -- in particular every field of every other
   member that does not overlap it -- keeps its value. Which members are
   readable is a property of the bytes: a member is readable when the bytes
   under each of its fields are plain (initialised and provenance-free), and
   its value is then what those bytes decode to.

   This module is the part that does not depend on the union: the views of
   integer and integer-array ranges with their two lemmas, and the leaf loads
   and stores at a constant offset into a range. PAL generates the views of
   structures and the union modules from these -- see `palow.md`.

   The implementation assumes nothing.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
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
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64
module M = FStar.Math.Lemmas

val slice_slice (b: bytes) (i: nat) (j: nat { i <= j /\ j <= len b })
                (k: nat) (l: nat { k <= l /\ l <= j - i })
  : Lemma (slice (slice b i j) k l == slice b (i + k) (i + l))
          [SMTPat (slice (slice b i j) k l)]

val slice_full (b: bytes)
  : Lemma (slice b 0 (len b) == b)
          [SMTPat (slice b 0 (len b))]

(* Writing a range back over itself changes nothing: what a member handed out
   whole and handed back unchanged does to the union. The pattern is the
   term the generated code produces, `+` and all. *)
#push-options "--warn_error -271"
val overlay_slice (b: bytes) (o: nat) (n: nat { o + n <= len b })
  : Lemma (overlay b 0 (slice b o (o + n)) o == b)
          [SMTPat (overlay b 0 (slice b o (o + n)) o)]
#pop-options

(* What putting a member's bytes back in front of the rest of the union is. *)
val append_overlay (u: bytes) (c: bytes { len c <= len u })
  : Lemma (append c (slice u (len c) (len u)) == overlay u 0 c 0)

(* A range inside a plain range is plain: how a read of one array element
   learns it from the member view that says the whole array is. *)
val plain_sub (b: bytes) (i: nat) (j: nat { i <= j /\ j <= len b })
              (k: nat) (l: nat { i <= k /\ k <= l /\ l <= j })
  : Lemma (requires plain (slice b i j)) (ensures plain (slice b k l))
          [SMTPat (plain (slice b i j)); SMTPat (plain (slice b k l))]

(* Two plain ranges side by side. *)
val plain_split (b: bytes) (k: nat { k <= len b })
  : Lemma (requires plain (slice b 0 k) /\ plain (slice b k (len b)))
          (ensures  plain b)

(* ---------------------------------------------------------------------------
   Arrays of integers

   The view of an array range is the sequence of its element views. An array
   of integers is readable exactly when its whole range is plain.
   --------------------------------------------------------------------------- *)
let array_view (#t: Type) (esize: pos) (n: nat) (f: bytes -> t)
               (b: bytes { len b == esize * n })
  : s: Seq.seq t { Seq.length s == n }
  = Seq.init n (fun (i: nat { i < n }) -> f (slice b (esize * i) (esize * i + esize)))

val elem_in (esize: pos) (n: nat) (i: nat { i < n })
  : Lemma (esize * i + esize <= esize * n)

val array_view_repr (#t: Type) (t_repr: t -> bytes -> prop) (esize: pos) (n: nat)
                    (f: bytes -> t) (b: bytes { len b == esize * n })
  : Lemma (requires plain b /\ (forall (c: bytes). plain c /\ len c == esize ==> t_repr (f c) c))
          (ensures  array_repr_o t_repr esize (array_view esize n f b) b)

(* The view of a byte array determines its bytes, when they are plain: what
   lets a caller that lent a member, and was promised its byte array back
   element by element, conclude that the union's bytes there are unchanged. *)
val uint8_array_view_inj (n: nat) (b1 b2: bytes)
  : Lemma (requires len b1 == n /\ len b2 == n /\ plain b1 /\ plain b2 /\
                    (forall (i: nat). i < n ==>
                       Seq.index (array_view 1 n uint8_t_of_bytes b1) i ==
                       Seq.index (array_view 1 n uint8_t_of_bytes b2) i))
          (ensures  b1 == b2)

(* The form the prover uses: for a byte array at offset `o` of two runs of
   bytes, in the shape a C contract
   `_forall(size_t k, k < n ==> a[k] == _old(a[k]))` takes (quantified over
   `size_t`, comparing `UInt8.v`), every range of bytes inside the array is
   the same in both. Stated per range, triggered by the range, because that
   is what the view of another member reads: a field of another view inside
   the array is a `slice u k l`, not a slice of the array. The patterns are
   the terms the generated code produces, `+` and all. *)
#push-options "--warn_error -271"
val uint8_array_view_inj_at (n: nat) (u1 u2: bytes) (o: nat { o + n <= len u1 /\ o + n <= len u2 })
  : Lemma (requires n < pow2 16 /\ plain (slice u1 o (o + n)) /\ plain (slice u2 o (o + n)) /\
                    (forall (k: SZ.t). SZ.v k < n ==>
                       U8.v (Seq.index (array_view 1 n uint8_t_of_bytes (slice u1 o (o + n))) (SZ.v k)) ==
                       U8.v (Seq.index (array_view 1 n uint8_t_of_bytes (slice u2 o (o + n))) (SZ.v k))))
          (ensures  forall (k l: nat). {:pattern (slice u1 k l)}
                      o <= k /\ k <= l /\ l <= o + n ==> slice u1 k l == slice u2 k l)
          [SMTPat (array_view 1 n uint8_t_of_bytes (slice u1 o (o + n)));
           SMTPat (array_view 1 n uint8_t_of_bytes (slice u2 o (o + n)))]
#pop-options

val elem_cover (esize: pos) (n: nat) (j: nat { j < esize * n })
  : Lemma (j / esize < n /\ esize * (j / esize) <= j /\ j < esize * (j / esize) + esize)

val array_repr_view (#t: Type) (t_repr: t -> bytes -> prop) (esize: pos) (n: nat)
                    (f: bytes -> t) (xs: Seq.seq t) (b: bytes { len b == esize * n })
  : Lemma (requires array_repr_o t_repr esize xs b /\ Seq.length xs == n /\
                    (forall (x: t) (c: bytes). t_repr x c ==> plain c /\ f c == x))
          (ensures  plain b /\ array_view esize n f b == xs)

(* ---------------------------------------------------------------------------
   Per integer type: the view of a range and the two lemmas, and the leaf load
   and store at offset `o` into a range `u` whose base is `al`-aligned. The
   offset of an integer field in an unpacked aggregate is a multiple of its
   size, and the aggregate's alignment is too, which is all the alignment of
   the field's address needs.
   --------------------------------------------------------------------------- *)

(* uint8_t *)
val uint8_t_view_repr (b: bytes)
  : Lemma (requires plain b /\ len b == 1) (ensures uint8_t_repr (uint8_t_of_bytes b) b)

val uint8_t_repr_view (x: U8.t) (b: bytes)
  : Lemma (requires uint8_t_repr x b) (ensures plain b /\ len b == 1 /\ uint8_t_of_bytes b == x)

val uint8_t_view_repr_all (_: unit)
  : Lemma (forall (c: bytes). plain c /\ len c == 1 ==> uint8_t_repr (uint8_t_of_bytes c) c)

val uint8_t_repr_view_all (_: unit)
  : Lemma (forall (x: U8.t) (c: bytes). uint8_t_repr x c ==> plain c /\ uint8_t_of_bytes c == x)

fn ov_uint8_t_read (a: ptr) (al: SZ.t) (o: SZ.t) (#p: perm) (#u: erased bytes)
  preserves mem_pts_to a p u
  requires pure (SZ.v o + 1 <= len u /\ SZ.fits (SZ.v o + 1) /\ aligned a al /\
                 SZ.v al % 1 == 0 /\ SZ.v o % 1 == 0 /\
                 plain (slice u (SZ.v o) (SZ.v o + 1)))
  returns  x : U8.t
  ensures  pure (SZ.v o + 1 <= len u /\ x == uint8_t_of_bytes (slice u (SZ.v o) (SZ.v o + 1)))

fn ov_uint8_t_write (a: ptr) (al: SZ.t) (o: SZ.t) (x: U8.t) (#u: erased bytes)
  requires mem_pts_to a 1.0R u
  requires pure (SZ.v o + 1 <= len u /\ SZ.fits (SZ.v o + 1) /\ aligned a al /\
                 SZ.v al % 1 == 0 /\ SZ.v o % 1 == 0)
  ensures  mem_pts_to a 1.0R (overlay u 0 (uint8_t_bytes x) (SZ.v o))

(* uint16_t *)
val uint16_t_view_repr (b: bytes)
  : Lemma (requires plain b /\ len b == 2) (ensures uint16_t_repr (uint16_t_of_bytes b) b)

val uint16_t_repr_view (x: U16.t) (b: bytes)
  : Lemma (requires uint16_t_repr x b) (ensures plain b /\ len b == 2 /\ uint16_t_of_bytes b == x)

val uint16_t_view_repr_all (_: unit)
  : Lemma (forall (c: bytes). plain c /\ len c == 2 ==> uint16_t_repr (uint16_t_of_bytes c) c)

val uint16_t_repr_view_all (_: unit)
  : Lemma (forall (x: U16.t) (c: bytes). uint16_t_repr x c ==> plain c /\ uint16_t_of_bytes c == x)

fn ov_uint16_t_read (a: ptr) (al: SZ.t) (o: SZ.t) (#p: perm) (#u: erased bytes)
  preserves mem_pts_to a p u
  requires pure (SZ.v o + 2 <= len u /\ SZ.fits (SZ.v o + 2) /\ aligned a al /\
                 SZ.v al % 2 == 0 /\ SZ.v o % 2 == 0 /\
                 plain (slice u (SZ.v o) (SZ.v o + 2)))
  returns  x : U16.t
  ensures  pure (SZ.v o + 2 <= len u /\ x == uint16_t_of_bytes (slice u (SZ.v o) (SZ.v o + 2)))

fn ov_uint16_t_write (a: ptr) (al: SZ.t) (o: SZ.t) (x: U16.t) (#u: erased bytes)
  requires mem_pts_to a 1.0R u
  requires pure (SZ.v o + 2 <= len u /\ SZ.fits (SZ.v o + 2) /\ aligned a al /\
                 SZ.v al % 2 == 0 /\ SZ.v o % 2 == 0)
  ensures  mem_pts_to a 1.0R (overlay u 0 (uint16_t_bytes x) (SZ.v o))

(* uint32_t *)
val uint32_t_view_repr (b: bytes)
  : Lemma (requires plain b /\ len b == 4) (ensures uint32_t_repr (uint32_t_of_bytes b) b)

val uint32_t_repr_view (x: U32.t) (b: bytes)
  : Lemma (requires uint32_t_repr x b) (ensures plain b /\ len b == 4 /\ uint32_t_of_bytes b == x)

val uint32_t_view_repr_all (_: unit)
  : Lemma (forall (c: bytes). plain c /\ len c == 4 ==> uint32_t_repr (uint32_t_of_bytes c) c)

val uint32_t_repr_view_all (_: unit)
  : Lemma (forall (x: U32.t) (c: bytes). uint32_t_repr x c ==> plain c /\ uint32_t_of_bytes c == x)

fn ov_uint32_t_read (a: ptr) (al: SZ.t) (o: SZ.t) (#p: perm) (#u: erased bytes)
  preserves mem_pts_to a p u
  requires pure (SZ.v o + 4 <= len u /\ SZ.fits (SZ.v o + 4) /\ aligned a al /\
                 SZ.v al % 4 == 0 /\ SZ.v o % 4 == 0 /\
                 plain (slice u (SZ.v o) (SZ.v o + 4)))
  returns  x : U32.t
  ensures  pure (SZ.v o + 4 <= len u /\ x == uint32_t_of_bytes (slice u (SZ.v o) (SZ.v o + 4)))

fn ov_uint32_t_write (a: ptr) (al: SZ.t) (o: SZ.t) (x: U32.t) (#u: erased bytes)
  requires mem_pts_to a 1.0R u
  requires pure (SZ.v o + 4 <= len u /\ SZ.fits (SZ.v o + 4) /\ aligned a al /\
                 SZ.v al % 4 == 0 /\ SZ.v o % 4 == 0)
  ensures  mem_pts_to a 1.0R (overlay u 0 (uint32_t_bytes x) (SZ.v o))

(* uint64_t *)
val uint64_t_view_repr (b: bytes)
  : Lemma (requires plain b /\ len b == 8) (ensures uint64_t_repr (uint64_t_of_bytes b) b)

val uint64_t_repr_view (x: U64.t) (b: bytes)
  : Lemma (requires uint64_t_repr x b) (ensures plain b /\ len b == 8 /\ uint64_t_of_bytes b == x)

val uint64_t_view_repr_all (_: unit)
  : Lemma (forall (c: bytes). plain c /\ len c == 8 ==> uint64_t_repr (uint64_t_of_bytes c) c)

val uint64_t_repr_view_all (_: unit)
  : Lemma (forall (x: U64.t) (c: bytes). uint64_t_repr x c ==> plain c /\ uint64_t_of_bytes c == x)

fn ov_uint64_t_read (a: ptr) (al: SZ.t) (o: SZ.t) (#p: perm) (#u: erased bytes)
  preserves mem_pts_to a p u
  requires pure (SZ.v o + 8 <= len u /\ SZ.fits (SZ.v o + 8) /\ aligned a al /\
                 SZ.v al % 8 == 0 /\ SZ.v o % 8 == 0 /\
                 plain (slice u (SZ.v o) (SZ.v o + 8)))
  returns  x : U64.t
  ensures  pure (SZ.v o + 8 <= len u /\ x == uint64_t_of_bytes (slice u (SZ.v o) (SZ.v o + 8)))

fn ov_uint64_t_write (a: ptr) (al: SZ.t) (o: SZ.t) (x: U64.t) (#u: erased bytes)
  requires mem_pts_to a 1.0R u
  requires pure (SZ.v o + 8 <= len u /\ SZ.fits (SZ.v o + 8) /\ aligned a al /\
                 SZ.v al % 8 == 0 /\ SZ.v o % 8 == 0)
  ensures  mem_pts_to a 1.0R (overlay u 0 (uint64_t_bytes x) (SZ.v o))

(* int8_t *)
val int8_t_view_repr (b: bytes)
  : Lemma (requires plain b /\ len b == 1) (ensures int8_t_repr (int8_t_of_bytes b) b)

val int8_t_repr_view (x: I8.t) (b: bytes)
  : Lemma (requires int8_t_repr x b) (ensures plain b /\ len b == 1 /\ int8_t_of_bytes b == x)

val int8_t_view_repr_all (_: unit)
  : Lemma (forall (c: bytes). plain c /\ len c == 1 ==> int8_t_repr (int8_t_of_bytes c) c)

val int8_t_repr_view_all (_: unit)
  : Lemma (forall (x: I8.t) (c: bytes). int8_t_repr x c ==> plain c /\ int8_t_of_bytes c == x)

fn ov_int8_t_read (a: ptr) (al: SZ.t) (o: SZ.t) (#p: perm) (#u: erased bytes)
  preserves mem_pts_to a p u
  requires pure (SZ.v o + 1 <= len u /\ SZ.fits (SZ.v o + 1) /\ aligned a al /\
                 SZ.v al % 1 == 0 /\ SZ.v o % 1 == 0 /\
                 plain (slice u (SZ.v o) (SZ.v o + 1)))
  returns  x : I8.t
  ensures  pure (SZ.v o + 1 <= len u /\ x == int8_t_of_bytes (slice u (SZ.v o) (SZ.v o + 1)))

fn ov_int8_t_write (a: ptr) (al: SZ.t) (o: SZ.t) (x: I8.t) (#u: erased bytes)
  requires mem_pts_to a 1.0R u
  requires pure (SZ.v o + 1 <= len u /\ SZ.fits (SZ.v o + 1) /\ aligned a al /\
                 SZ.v al % 1 == 0 /\ SZ.v o % 1 == 0)
  ensures  mem_pts_to a 1.0R (overlay u 0 (int8_t_bytes x) (SZ.v o))

(* int16_t *)
val int16_t_view_repr (b: bytes)
  : Lemma (requires plain b /\ len b == 2) (ensures int16_t_repr (int16_t_of_bytes b) b)

val int16_t_repr_view (x: I16.t) (b: bytes)
  : Lemma (requires int16_t_repr x b) (ensures plain b /\ len b == 2 /\ int16_t_of_bytes b == x)

val int16_t_view_repr_all (_: unit)
  : Lemma (forall (c: bytes). plain c /\ len c == 2 ==> int16_t_repr (int16_t_of_bytes c) c)

val int16_t_repr_view_all (_: unit)
  : Lemma (forall (x: I16.t) (c: bytes). int16_t_repr x c ==> plain c /\ int16_t_of_bytes c == x)

fn ov_int16_t_read (a: ptr) (al: SZ.t) (o: SZ.t) (#p: perm) (#u: erased bytes)
  preserves mem_pts_to a p u
  requires pure (SZ.v o + 2 <= len u /\ SZ.fits (SZ.v o + 2) /\ aligned a al /\
                 SZ.v al % 2 == 0 /\ SZ.v o % 2 == 0 /\
                 plain (slice u (SZ.v o) (SZ.v o + 2)))
  returns  x : I16.t
  ensures  pure (SZ.v o + 2 <= len u /\ x == int16_t_of_bytes (slice u (SZ.v o) (SZ.v o + 2)))

fn ov_int16_t_write (a: ptr) (al: SZ.t) (o: SZ.t) (x: I16.t) (#u: erased bytes)
  requires mem_pts_to a 1.0R u
  requires pure (SZ.v o + 2 <= len u /\ SZ.fits (SZ.v o + 2) /\ aligned a al /\
                 SZ.v al % 2 == 0 /\ SZ.v o % 2 == 0)
  ensures  mem_pts_to a 1.0R (overlay u 0 (int16_t_bytes x) (SZ.v o))

(* int32_t *)
val int32_t_view_repr (b: bytes)
  : Lemma (requires plain b /\ len b == 4) (ensures int32_t_repr (int32_t_of_bytes b) b)

val int32_t_repr_view (x: I32.t) (b: bytes)
  : Lemma (requires int32_t_repr x b) (ensures plain b /\ len b == 4 /\ int32_t_of_bytes b == x)

val int32_t_view_repr_all (_: unit)
  : Lemma (forall (c: bytes). plain c /\ len c == 4 ==> int32_t_repr (int32_t_of_bytes c) c)

val int32_t_repr_view_all (_: unit)
  : Lemma (forall (x: I32.t) (c: bytes). int32_t_repr x c ==> plain c /\ int32_t_of_bytes c == x)

fn ov_int32_t_read (a: ptr) (al: SZ.t) (o: SZ.t) (#p: perm) (#u: erased bytes)
  preserves mem_pts_to a p u
  requires pure (SZ.v o + 4 <= len u /\ SZ.fits (SZ.v o + 4) /\ aligned a al /\
                 SZ.v al % 4 == 0 /\ SZ.v o % 4 == 0 /\
                 plain (slice u (SZ.v o) (SZ.v o + 4)))
  returns  x : I32.t
  ensures  pure (SZ.v o + 4 <= len u /\ x == int32_t_of_bytes (slice u (SZ.v o) (SZ.v o + 4)))

fn ov_int32_t_write (a: ptr) (al: SZ.t) (o: SZ.t) (x: I32.t) (#u: erased bytes)
  requires mem_pts_to a 1.0R u
  requires pure (SZ.v o + 4 <= len u /\ SZ.fits (SZ.v o + 4) /\ aligned a al /\
                 SZ.v al % 4 == 0 /\ SZ.v o % 4 == 0)
  ensures  mem_pts_to a 1.0R (overlay u 0 (int32_t_bytes x) (SZ.v o))

(* int64_t *)
val int64_t_view_repr (b: bytes)
  : Lemma (requires plain b /\ len b == 8) (ensures int64_t_repr (int64_t_of_bytes b) b)

val int64_t_repr_view (x: I64.t) (b: bytes)
  : Lemma (requires int64_t_repr x b) (ensures plain b /\ len b == 8 /\ int64_t_of_bytes b == x)

val int64_t_view_repr_all (_: unit)
  : Lemma (forall (c: bytes). plain c /\ len c == 8 ==> int64_t_repr (int64_t_of_bytes c) c)

val int64_t_repr_view_all (_: unit)
  : Lemma (forall (x: I64.t) (c: bytes). int64_t_repr x c ==> plain c /\ int64_t_of_bytes c == x)

fn ov_int64_t_read (a: ptr) (al: SZ.t) (o: SZ.t) (#p: perm) (#u: erased bytes)
  preserves mem_pts_to a p u
  requires pure (SZ.v o + 8 <= len u /\ SZ.fits (SZ.v o + 8) /\ aligned a al /\
                 SZ.v al % 8 == 0 /\ SZ.v o % 8 == 0 /\
                 plain (slice u (SZ.v o) (SZ.v o + 8)))
  returns  x : I64.t
  ensures  pure (SZ.v o + 8 <= len u /\ x == int64_t_of_bytes (slice u (SZ.v o) (SZ.v o + 8)))

fn ov_int64_t_write (a: ptr) (al: SZ.t) (o: SZ.t) (x: I64.t) (#u: erased bytes)
  requires mem_pts_to a 1.0R u
  requires pure (SZ.v o + 8 <= len u /\ SZ.fits (SZ.v o + 8) /\ aligned a al /\
                 SZ.v al % 8 == 0 /\ SZ.v o % 8 == 0)
  ensures  mem_pts_to a 1.0R (overlay u 0 (int64_t_bytes x) (SZ.v o))
