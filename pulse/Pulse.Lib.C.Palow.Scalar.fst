module Pulse.Lib.C.Palow.Scalar

(* ---------------------------------------------------------------------------
   Palow layer 1: scalar types.

   Every typed owner retains actual per-byte metadata and read_ok for its C
   descriptor. Raw reveal returns that same index; claim/conceal require it,
   together with representation validity and alignment. Ordinary uninit
   forgets a value, not metadata, and is distinct from opaque preparation.

   Public convenience owners existentially hide the index. Effective.Value
   and Machine's indexed operations retain it explicitly when an enclosing
   aggregate or a C-call contract needs to preserve its identity.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow.Encoding
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Array

module ET = Pulse.Lib.C.Palow.Etype
module T = Pulse.Lib.C.Palow.Effective.Typed
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module M = FStar.Math.Lemmas

(* ---------------------------------------------------------------------------
   uint8_t
   --------------------------------------------------------------------------- *)



let uint8_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: U8.t) : slprop =
  T.value uint8_t_ctype uint8_t_repr uint8_t_alignof a p x

let uint8_t_repr_len (x: U8.t) (b: bytes)
  : Lemma (requires uint8_t_repr x b)
          (ensures  len b == SZ.v uint8_t_sizeof)
  = ()

ghost fn uint8_t_reveal (a: ptr) (#p: perm) (#x: U8.t)
  requires uint8_t_pts_to a p x
  ensures  exists* b e. mem_pts_to_at a p b e ** pure (ET.elen e == len b /\ ET.read_ok e uint8_t_ctype /\ uint8_t_repr x b /\ aligned a uint8_t_alignof)
{
  unfold uint8_t_pts_to a p x;
  T.reveal_value uint8_t_ctype uint8_t_repr uint8_t_alignof a;
}

ghost fn uint8_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: U8.t) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (uint8_t_repr x b)
  requires pure (aligned a uint8_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e uint8_t_ctype)
  ensures  uint8_t_pts_to a p x
{
  uint8_t_repr_len x b;
  T.claim uint8_t_ctype uint8_t_repr uint8_t_alignof a #p #x #b #e;
  fold uint8_t_pts_to a p x;
}

(* ---------------------------------------------------------------------------
   uint32_t
   --------------------------------------------------------------------------- *)



let uint32_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: U32.t) : slprop =
  T.value uint32_t_ctype uint32_t_repr uint32_t_alignof a p x

let uint32_t_repr_len (x: U32.t) (b: bytes)
  : Lemma (requires uint32_t_repr x b)
          (ensures  len b == SZ.v uint32_t_sizeof)
  = ()

(* Unknown contents with retained type admissibility. This is not a pending
   incompatible write reservation. *)
let uint32_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop =
  T.storage uint32_t_ctype uint32_t_alignof a

(* An integer object carries no provenance: this is what distinguishes it from
   a stored pointer with the same bit pattern, and is why writing an integer
   over a stored pointer makes the pointer unrecoverable. *)
let uint32_t_repr_no_prov (x: U32.t) (b: bytes)
  : Lemma (requires uint32_t_repr x b)
          (ensures  no_prov b /\ initialized b)
  = ()

let uint32_t_repr_injective (x y: U32.t) (b: bytes)
  : Lemma (requires uint32_t_repr x b /\ uint32_t_repr y b)
          (ensures  x == y)
  = assert_norm (pow2 (8 * 4) == pow2 32);
    encode_injective (SZ.v uint32_t_sizeof) None (U32.v x) (U32.v y)

(* ---------------------------------------------------------------------------
   Derived resource facts

   These are the properties PAL's proof automation actually consumes, and the
   point of proving them here is that they are *consequences* of the layer-0
   interface rather than further axioms.
   --------------------------------------------------------------------------- *)

ghost fn uint32_t_pts_to_not_null (a: ptr) (#p: perm) (#x: U32.t)
  preserves uint32_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))
{
  unfold uint32_t_pts_to a p x;
  T.not_null uint32_t_ctype uint32_t_repr uint32_t_alignof a;
  fold uint32_t_pts_to a p x;
}

[@@allow_ambiguous]
ghost fn uint32_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: U32.t)
  preserves uint32_t_pts_to a p1 x
  preserves uint32_t_pts_to a p2 y
  ensures   pure (x == y)
{
  unfold uint32_t_pts_to a p1 x;
  unfold uint32_t_pts_to a p2 y;
  T.agree uint32_t_ctype uint32_t_repr uint32_t_alignof uint32_t_repr_injective a;
  fold uint32_t_pts_to a p1 x;
  fold uint32_t_pts_to a p2 y;
}

ghost fn uint32_t_share (a: ptr) (#p: perm) (#x: U32.t)
  requires uint32_t_pts_to a p x
  ensures  uint32_t_pts_to a (p /. 2.0R) x ** uint32_t_pts_to a (p /. 2.0R) x
{
  unfold uint32_t_pts_to a p x;
  T.share uint32_t_ctype uint32_t_repr uint32_t_alignof a;
  fold uint32_t_pts_to a (p /. 2.0R) x;
  fold uint32_t_pts_to a (p /. 2.0R) x;
}

[@@allow_ambiguous]
ghost fn uint32_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: U32.t)
  requires uint32_t_pts_to a p1 x ** uint32_t_pts_to a p2 y
  ensures  uint32_t_pts_to a (p1 +. p2) x ** pure (x == y)
{
  unfold uint32_t_pts_to a p1 x;
  unfold uint32_t_pts_to a p2 y;
  T.gather uint32_t_ctype uint32_t_repr uint32_t_alignof uint32_t_repr_injective a;
  fold uint32_t_pts_to a (p1 +. p2) x;
}

(* Reveal the byte-level view of a scalar object, and put it back. This pair is
   the escape hatch the whole design exists for: it is what a custom allocator
   or a type pun goes through, and it is a definitional unfolding rather than
   an axiom. *)
ghost fn uint32_t_reveal (a: ptr) (#p: perm) (#x: U32.t)
  requires uint32_t_pts_to a p x
  ensures  exists* b e. mem_pts_to_at a p b e ** pure (ET.elen e == len b /\ ET.read_ok e uint32_t_ctype /\ uint32_t_repr x b /\ aligned a uint32_t_alignof)
{
  unfold uint32_t_pts_to a p x;
  T.reveal_value uint32_t_ctype uint32_t_repr uint32_t_alignof a;
}

ghost fn uint32_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#x: U32.t) (#e: ET.etypes)
  requires mem_pts_to_at a p b e
  requires pure (uint32_t_repr x b)
  requires pure (aligned a uint32_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e uint32_t_ctype)
  ensures  uint32_t_pts_to a p x
{
  uint32_t_repr_len x b;
  T.claim uint32_t_ctype uint32_t_repr uint32_t_alignof a #p #x #b #e;
  fold uint32_t_pts_to a p x;
}

(* Forget the value of an object, recovering the write-only view. Needed to hand
   a local back to `uint32_t_stack_free`, which must not care what was last
   stored in it. *)
ghost fn uint32_t_forget (a: ptr) (#x: U32.t)
  requires uint32_t_pts_to a 1.0R x
  ensures  uint32_t_pts_to_uninit a
{
  unfold uint32_t_pts_to a 1.0R x;
  T.forget uint32_t_ctype uint32_t_repr uint32_t_alignof a;
  fold uint32_t_pts_to_uninit a;
}

ghost fn uint32_t_claim_uninit (a: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v uint32_t_sizeof /\ aligned a uint32_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e uint32_t_ctype)
  ensures  uint32_t_pts_to_uninit a
{
  T.claim_storage uint32_t_ctype uint32_t_alignof a;
  fold uint32_t_pts_to_uninit a;
}

(* Raw storage of the right size can be claimed as a `uint32_t` object as soon as
   we can exhibit a value it represents. This is the step a custom allocator
   takes when it hands out a chunk of a block it carved up. *)
ghost fn uint32_t_claim (a: ptr) (#b: bytes) (x: U32.t) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (uint32_t_repr x b)
  requires pure (aligned a uint32_t_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e uint32_t_ctype)
  ensures  uint32_t_pts_to a 1.0R x
{
  uint32_t_repr_len x b;
  T.claim uint32_t_ctype uint32_t_repr uint32_t_alignof a #1.0R #x #b #e;
  fold uint32_t_pts_to a 1.0R x;
}

ghost fn uint32_t_reveal_uninit (a: ptr)
  requires uint32_t_pts_to_uninit a
  ensures  exists* b e. mem_pts_to_at a 1.0R b e ** pure (ET.elen e == len b /\ ET.read_ok e uint32_t_ctype /\ len b == SZ.v uint32_t_sizeof /\ aligned a uint32_t_alignof)
{
  unfold uint32_t_pts_to_uninit a;
  T.reveal_storage uint32_t_ctype uint32_t_alignof a;
}

(* ---------------------------------------------------------------------------
   Pointers as stored values

   This is where putting provenance in the bytes pays for itself. A stored
   pointer's object representation is the target-endian bytes of its address,
   each carrying the pointer's provenance -- so `ptr_repr` is *defined*, not
   axiomatized, and three facts that would otherwise each need an axiom become
   consequences of the definition:

   - a stored pointer is recovered exactly, provenance included
     (`ptr_repr_injective`);
   - overwriting it with an integer makes it unrecoverable, because integer
     representations carry no provenance (`ptr_repr_no_prov`);
   - a byte-wise copy preserves it, because copying bytes copies provenance
     (see `Pulse.Lib.C.Palow.Provenance`).

   Under a model where bytes are plain `uint8_t`s, the first and third are
   indistinguishable from the second, and there is no way to say which of them
   should hold.
   --------------------------------------------------------------------------- *)



let ptr_pts_to ([@@@mkey] dest: ptr) (p: perm) (a: ptr) : slprop =
  T.value ptr_ctype ptr_repr ptr_alignof dest p a

let ptr_repr_len (a: ptr) (b: bytes)
  : Lemma (requires ptr_repr a b)
          (ensures  len b == SZ.v ptr_sizeof /\ initialized b /\
                    has_prov (prov_of a) b)
  = ()

let ptr_repr_injective (a1 a2: ptr) (b: bytes)
  : Lemma (requires ptr_repr a1 b /\ ptr_repr a2 b)
          (ensures  a1 == a2)
  = assert_norm (pow2 (8 * 8) == pow2 64);
    assert (get b 0 == byte_at (prov_of a1) (addr_of a1) 0);
    assert (get b 0 == byte_at (prov_of a2) (addr_of a2) 0);
    addr_bound a1;
    addr_bound a2;
    encode_injective (SZ.v ptr_sizeof) (prov_of a1) (addr_of a1) (addr_of a2);
    ptr_ext a1 a2

(* Writing an integer over a stored pointer strips the provenance of the bytes
   it covers, and no pointer derived from an allocation is represented by
   provenance-free bytes. So the only pointer still recoverable from those bytes
   is one with the empty provenance, which cannot be dereferenced. *)
let ptr_repr_no_prov (a: ptr) (b: bytes)
  : Lemma (requires ptr_repr a b /\ no_prov b)
          (ensures  prov_of a == None)
  = ()

ghost fn ptr_pts_to_not_null (dest: ptr) (#p: perm) (#a: ptr)
  preserves ptr_pts_to dest p a
  ensures   pure (not (is_null dest) /\ Some? (prov_of dest))
{
  unfold ptr_pts_to dest p a;
  T.not_null ptr_ctype ptr_repr ptr_alignof dest;
  fold ptr_pts_to dest p a;
}

[@@allow_ambiguous]
ghost fn ptr_agree (dest: ptr) (#p1 #p2: perm) (#a1 #a2: ptr)
  preserves ptr_pts_to dest p1 a1
  preserves ptr_pts_to dest p2 a2
  ensures   pure (a1 == a2)
{
  unfold ptr_pts_to dest p1 a1;
  unfold ptr_pts_to dest p2 a2;
  T.agree ptr_ctype ptr_repr ptr_alignof ptr_repr_injective dest;
  fold ptr_pts_to dest p1 a1;
  fold ptr_pts_to dest p2 a2;
}

ghost fn ptr_share (dest: ptr) (#p: perm) (#a: ptr)
  requires ptr_pts_to dest p a
  ensures  ptr_pts_to dest (p /. 2.0R) a ** ptr_pts_to dest (p /. 2.0R) a
{
  unfold ptr_pts_to dest p a;
  T.share ptr_ctype ptr_repr ptr_alignof dest;
  fold ptr_pts_to dest (p /. 2.0R) a;
  fold ptr_pts_to dest (p /. 2.0R) a;
}

[@@allow_ambiguous]
ghost fn ptr_gather (dest: ptr) (#p1 #p2: perm) (#a1 #a2: ptr)
  requires ptr_pts_to dest p1 a1 ** ptr_pts_to dest p2 a2
  ensures  ptr_pts_to dest (p1 +. p2) a1 ** pure (a1 == a2)
{
  unfold ptr_pts_to dest p1 a1;
  unfold ptr_pts_to dest p2 a2;
  T.gather ptr_ctype ptr_repr ptr_alignof ptr_repr_injective dest;
  fold ptr_pts_to dest (p1 +. p2) a1;
}

ghost fn ptr_reveal (dest: ptr) (#p: perm) (#a: ptr)
  requires ptr_pts_to dest p a
  ensures  exists* b e. mem_pts_to_at dest p b e ** pure (ET.elen e == len b /\ ET.read_ok e ptr_ctype /\ ptr_repr a b /\ aligned dest ptr_alignof)
{
  unfold ptr_pts_to dest p a;
  T.reveal_value ptr_ctype ptr_repr ptr_alignof dest;
}

ghost fn ptr_conceal (dest: ptr) (#p: perm) (#b: bytes) (#a: ptr) (#e: ET.etypes)
  requires mem_pts_to_at dest p b e
  requires pure (ptr_repr a b)
  requires pure (aligned dest ptr_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e ptr_ctype)
  ensures  ptr_pts_to dest p a
{
  ptr_repr_len a b;
  T.claim ptr_ctype ptr_repr ptr_alignof dest #p #a #b #e;
  fold ptr_pts_to dest p a;
}

(* A pointer-typed local, before anything has been stored in it. This is the
   same `_pts_to_uninit`/`_forget` pair every scalar type has; it exists so the
   translator can allocate and release a local without a case for pointers. *)
let ptr_pts_to_uninit ([@@@mkey] dest: ptr) : slprop =
  T.storage ptr_ctype ptr_alignof dest

ghost fn ptr_forget (dest: ptr) (#a: ptr)
  requires ptr_pts_to dest 1.0R a
  ensures  ptr_pts_to_uninit dest
{
  unfold ptr_pts_to dest 1.0R a;
  T.forget ptr_ctype ptr_repr ptr_alignof dest;
  fold ptr_pts_to_uninit dest;
}

ghost fn ptr_claim_uninit (dest: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at dest 1.0R b e
  requires pure (len b == SZ.v ptr_sizeof /\ aligned dest ptr_alignof)
  requires pure (ET.elen e == len b /\ ET.read_ok e ptr_ctype)
  ensures  ptr_pts_to_uninit dest
{
  T.claim_storage ptr_ctype ptr_alignof dest;
  fold ptr_pts_to_uninit dest;
}

ghost fn ptr_reveal_uninit (dest: ptr)
  requires ptr_pts_to_uninit dest
  ensures  exists* b e. mem_pts_to_at dest 1.0R b e ** pure (ET.elen e == len b /\ ET.read_ok e ptr_ctype /\ len b == SZ.v ptr_sizeof /\ aligned dest ptr_alignof)
{
  unfold ptr_pts_to_uninit dest;
  T.reveal_storage ptr_ctype ptr_alignof dest;
}

(* ---------------------------------------------------------------------------
   Elements of an array

   `array_focus` hands back an `elem_pts_to t_ctype t_repr`, which is the generic
   "there exist bytes representing this value" form. Every scalar type has its
   own points-to predicate instead, so each one gets a pair of ghost functions
   trading between the two. They are what makes an emitted subscript short: the
   value stays implicit throughout, so PAL never has to name `Seq.index xs i`.
   --------------------------------------------------------------------------- *)

ghost fn uint8_t_of_elem (a: ptr) (#p: perm) (#x: U8.t)
  requires elem_pts_to uint8_t_ctype uint8_t_repr a p x
  requires pure (aligned a uint8_t_alignof)
  ensures  uint8_t_pts_to a p x
{
  elem_reveal uint8_t_ctype uint8_t_repr a;
  uint8_t_conceal a #p #_ #x;
}

ghost fn uint8_t_to_elem (a: ptr) (#p: perm) (#x: U8.t)
  requires uint8_t_pts_to a p x
  ensures  elem_pts_to uint8_t_ctype uint8_t_repr a p x
  ensures  pure (aligned a uint8_t_alignof)
{
  uint8_t_reveal a;
  elem_conceal uint8_t_ctype uint8_t_repr a #p #_ #x;
}

ghost fn uint32_t_of_elem (a: ptr) (#p: perm) (#x: U32.t)
  requires elem_pts_to uint32_t_ctype uint32_t_repr a p x
  requires pure (aligned a uint32_t_alignof)
  ensures  uint32_t_pts_to a p x
{
  elem_reveal uint32_t_ctype uint32_t_repr a;
  uint32_t_conceal a #p #_ #x;
}

ghost fn uint32_t_to_elem (a: ptr) (#p: perm) (#x: U32.t)
  requires uint32_t_pts_to a p x
  ensures  elem_pts_to uint32_t_ctype uint32_t_repr a p x
  ensures  pure (aligned a uint32_t_alignof)
{
  uint32_t_reveal a;
  elem_conceal uint32_t_ctype uint32_t_repr a #p #_ #x;
}

ghost fn ptr_of_elem (a: ptr) (#p: perm) (#x: ptr)
  requires elem_pts_to ptr_ctype ptr_repr a p x
  requires pure (aligned a ptr_alignof)
  ensures  ptr_pts_to a p x
{
  elem_reveal ptr_ctype ptr_repr a;
  ptr_conceal a #p #_ #x;
}

ghost fn ptr_to_elem (a: ptr) (#p: perm) (#x: ptr)
  requires ptr_pts_to a p x
  ensures  elem_pts_to ptr_ctype ptr_repr a p x
  ensures  pure (aligned a ptr_alignof)
{
  ptr_reveal a;
  elem_conceal ptr_ctype ptr_repr a #p #_ #x;
}
