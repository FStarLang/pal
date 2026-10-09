module Pulse.Lib.C.Palow.Scalar

(* ---------------------------------------------------------------------------
   Palow layer 1: scalar types.

   For each C scalar type we give a representation relation and a typed
   points-to predicate *defined* in terms of `mem_pts_to`. PAL will emit one
   copy of this per translated C type; the two instances here (`uint8_t` and
   `uint32_t`) exist to check that the layer-0 interface actually supports the
   derivation, and to be the leaves of the aggregate proofs in
   `Pulse.Lib.C.Palow.Aggregate`.

   Note that a scalar's representation is *unique*: an unsigned integer type
   with no padding bits has exactly one object representation per value, so the
   points-to predicate needs no existential over the bytes. The general
   `exists* b. mem_pts_to a p b ** pure (t_repr x b)` shape from `palow.md` is
   only needed where the representation is not unique -- aggregates with
   padding, and unions.

   The predicates are ordinary `let`s, so Pulse will not unfold them
   automatically; proofs that need to see the bytes use `unfold`/`fold`
   explicitly. That is deliberate: unfolding everywhere would pollute the
   context, and the pointee has to stay resolvable from a `mem_pts_to`-free
   context for nested dereferences to work.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow.Encoding
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Index
open Pulse.Lib.C.Palow.Array

module SZ = FStar.SizeT
module ET = Pulse.Lib.C.Palow.Etype
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module M = FStar.Math.Lemmas

(* An all-zero range is the encoding of the value zero, at any width. This is
   what makes `calloc` different from `malloc`: the storage arrives already
   representing a value, so it may be read before it is written.

   It carries no `SMTPat`. The fact is wanted at `encode n None (I32.v 0l)` and
   the like, which is not syntactically `encode n None 0`, so a pattern would
   not fire where it matters; the caller names it instead. *)
let encode_zero (n: nat)
  : Lemma (encode n None 0 == zeroed n)
  = Seq.lemma_eq_elim (encode n None 0) (zeroed n)

(* ---------------------------------------------------------------------------
   uint8_t
   --------------------------------------------------------------------------- *)

let uint8_t_sizeof : SZ.t = 1sz
let uint8_t_alignof : SZ.t = 1sz
  (* `uint8_t` is `unsigned char`, a character type: it may alias anything. *)
let uint8_t_ctype : ET.ctype = ET.TScalar ET.SChar

(* The effective-type side condition a `uint8_t` object's storage has to meet,
   under the name every type publishes so that a struct or union containing
   one can state its own condition without knowing what kind of type it is. *)
let uint8_t_etype_ok (e: ET.etypes) : prop = ET.read_ok e uint8_t_ctype /\ ET.allocated e

let uint8_t_etype_ok_none ()
  : Lemma (uint8_t_etype_ok (ET.etypes_none (SZ.v uint8_t_sizeof)))
  = ()

let uint8_t_etype_ok_untyped (e: ET.etypes)
  : Lemma (requires ET.untyped e /\ ET.elen e == SZ.v uint8_t_sizeof)
          (ensures  uint8_t_etype_ok e)
  = ET.untyped_read_ok e uint8_t_ctype; ET.allocated_untyped e

(* Storage that a store at this type has just produced meets its condition.
   This is where a union member switch lands. *)
let uint8_t_etype_ok_read_ok_all (_: unit)
  : Lemma (forall (e: ET.etypes). ET.read_ok e uint8_t_ctype /\ ET.allocated e
                             /\ ET.elen e == SZ.v uint8_t_sizeof ==> uint8_t_etype_ok e)
  = ()

(* The same, quantified: an array of this type needs it under a binder. *)
let uint8_t_etype_ok_untyped_all (_: unit)
  : Lemma (forall (e: ET.etypes). ET.untyped e /\ ET.elen e == SZ.v uint8_t_sizeof ==> uint8_t_etype_ok e)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires uint8_t_etype_ok_untyped)


let uint8_t_repr (x: U8.t) (b: bytes) : prop =
  b == encode (SZ.v uint8_t_sizeof) None (U8.v x)

val uint8_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: U8.t) : slprop


val uint8_t_repr_len (x: U8.t) (b: bytes)
  : Lemma (requires uint8_t_repr x b)
          (ensures  len b == SZ.v uint8_t_sizeof)


ghost fn uint8_t_reveal (a: ptr) (#p: perm) (#x: U8.t)
  requires uint8_t_pts_to a p x
  ensures  exists* b e. mem_pts_to_at a p b e
             ** pure (uint8_t_repr x b /\ aligned a uint8_t_alignof
                      /\ ET.elen e == len b /\ uint8_t_etype_ok e)


ghost fn uint8_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#e: ET.etypes) (#x: U8.t)
  requires mem_pts_to_at a p b e
  requires pure (uint8_t_repr x b)
  requires pure (aligned a uint8_t_alignof)
  requires pure (ET.elen e == len b /\ uint8_t_etype_ok e)
  ensures  uint8_t_pts_to a p x


(* ---------------------------------------------------------------------------
   uint32_t
   --------------------------------------------------------------------------- *)

let uint32_t_sizeof : SZ.t = 4sz
let uint32_t_alignof : SZ.t = 4sz
let uint32_t_ctype : ET.ctype = ET.TScalar ET.SUInt32

(* The effective-type side condition a `uint32_t` object's storage has to meet,
   under the name every type publishes so that a struct or union containing
   one can state its own condition without knowing what kind of type it is. *)
let uint32_t_etype_ok (e: ET.etypes) : prop = ET.read_ok e uint32_t_ctype /\ ET.allocated e

let uint32_t_etype_ok_none ()
  : Lemma (uint32_t_etype_ok (ET.etypes_none (SZ.v uint32_t_sizeof)))
  = ()

let uint32_t_etype_ok_untyped (e: ET.etypes)
  : Lemma (requires ET.untyped e /\ ET.elen e == SZ.v uint32_t_sizeof)
          (ensures  uint32_t_etype_ok e)
  = ET.untyped_read_ok e uint32_t_ctype; ET.allocated_untyped e

(* Storage that a store at this type has just produced meets its condition.
   This is where a union member switch lands. *)
let uint32_t_etype_ok_read_ok_all (_: unit)
  : Lemma (forall (e: ET.etypes). ET.read_ok e uint32_t_ctype /\ ET.allocated e
                             /\ ET.elen e == SZ.v uint32_t_sizeof ==> uint32_t_etype_ok e)
  = ()

(* The same, quantified: an array of this type needs it under a binder. *)
let uint32_t_etype_ok_untyped_all (_: unit)
  : Lemma (forall (e: ET.etypes). ET.untyped e /\ ET.elen e == SZ.v uint32_t_sizeof ==> uint32_t_etype_ok e)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires uint32_t_etype_ok_untyped)


let uint32_t_repr (x: U32.t) (b: bytes) : prop =
  b == encode (SZ.v uint32_t_sizeof) None (U32.v x)

val uint32_t_pts_to ([@@@mkey] a: ptr) (p: perm) (x: U32.t) : slprop


val uint32_t_repr_len (x: U32.t) (b: bytes)
  : Lemma (requires uint32_t_repr x b)
          (ensures  len b == SZ.v uint32_t_sizeof)


(* Write-only ownership of storage that is the right size for a `uint32_t` but
   whose contents we know nothing about: what a stack allocation hands out, and
   what a deallocation takes back. *)
val uint32_t_pts_to_uninit ([@@@mkey] a: ptr) : slprop


(* An integer object carries no provenance: this is what distinguishes it from
   a stored pointer with the same bit pattern, and is why writing an integer
   over a stored pointer makes the pointer unrecoverable. *)
val uint32_t_repr_no_prov (x: U32.t) (b: bytes)
  : Lemma (requires uint32_t_repr x b)
          (ensures  no_prov b /\ initialized b)


val uint32_t_repr_injective (x y: U32.t) (b: bytes)
  : Lemma (requires uint32_t_repr x b /\ uint32_t_repr y b)
          (ensures  x == y)


(* ---------------------------------------------------------------------------
   Derived resource facts

   These are the properties PAL's proof automation actually consumes, and the
   point of proving them here is that they are *consequences* of the layer-0
   interface rather than further axioms.
   --------------------------------------------------------------------------- *)

ghost fn uint32_t_pts_to_not_null (a: ptr) (#p: perm) (#x: U32.t)
  preserves uint32_t_pts_to a p x
  ensures   pure (not (is_null a) /\ Some? (prov_of a))


[@@allow_ambiguous]
ghost fn uint32_t_agree (a: ptr) (#p1 #p2: perm) (#x #y: U32.t)
  preserves uint32_t_pts_to a p1 x
  preserves uint32_t_pts_to a p2 y
  ensures   pure (x == y)


ghost fn uint32_t_share (a: ptr) (#p: perm) (#x: U32.t)
  requires uint32_t_pts_to a p x
  ensures  uint32_t_pts_to a (p /. 2.0R) x ** uint32_t_pts_to a (p /. 2.0R) x


[@@allow_ambiguous]
ghost fn uint32_t_gather (a: ptr) (#p1 #p2: perm) (#x #y: U32.t)
  requires uint32_t_pts_to a p1 x ** uint32_t_pts_to a p2 y
  ensures  uint32_t_pts_to a (p1 +. p2) x ** pure (x == y)


(* Reveal the byte-level view of a scalar object, and put it back. This pair is
   the escape hatch the whole design exists for: it is what a custom allocator
   or a type pun goes through, and it is a definitional unfolding rather than
   an axiom. *)
ghost fn uint32_t_reveal (a: ptr) (#p: perm) (#x: U32.t)
  requires uint32_t_pts_to a p x
  ensures  exists* b e. mem_pts_to_at a p b e
             ** pure (uint32_t_repr x b /\ aligned a uint32_t_alignof
                      /\ ET.elen e == len b /\ uint32_t_etype_ok e)


ghost fn uint32_t_conceal (a: ptr) (#p: perm) (#b: bytes) (#e: ET.etypes) (#x: U32.t)
  requires mem_pts_to_at a p b e
  requires pure (uint32_t_repr x b)
  requires pure (aligned a uint32_t_alignof)
  requires pure (ET.elen e == len b /\ uint32_t_etype_ok e)
  ensures  uint32_t_pts_to a p x


(* Forget the value of an object, recovering the write-only view. Needed to hand
   a local back to `uint32_t_stack_free`, which must not care what was last
   stored in it. *)
ghost fn uint32_t_forget (a: ptr) (#x: U32.t)
  requires uint32_t_pts_to a 1.0R x
  ensures  uint32_t_pts_to_uninit a


ghost fn uint32_t_claim_uninit (a: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == SZ.v uint32_t_sizeof /\ aligned a uint32_t_alignof)
  requires pure (ET.elen e == len b /\ uint32_t_etype_ok e)
  ensures  uint32_t_pts_to_uninit a


(* Raw storage of the right size can be claimed as a `uint32_t` object as soon as
   we can exhibit a value it represents. This is the step a custom allocator
   takes when it hands out a chunk of a block it carved up. *)
ghost fn uint32_t_claim (a: ptr) (#b: bytes) (#e: ET.etypes) (x: U32.t)
  requires mem_pts_to_at a 1.0R b e
  requires pure (uint32_t_repr x b)
  requires pure (aligned a uint32_t_alignof)
  requires pure (ET.elen e == len b /\ uint32_t_etype_ok e)
  ensures  uint32_t_pts_to a 1.0R x


(* And the reverse of `claim_uninit`: an allocation's block has to be handed
   back to `free` as bytes, so write-only ownership has to be spendable. *)
ghost fn uint32_t_reveal_uninit (a: ptr)
  requires uint32_t_pts_to_uninit a
  ensures  exists* b. mem_pts_to a 1.0R b ** pure (len b == SZ.v uint32_t_sizeof /\ aligned a uint32_t_alignof)

(* The same, keeping the effective-type index. The bytes a stack allocation
   hands out already meet the type's condition -- that is what
   `uint32_t_pts_to_uninit` says -- and a byte-level copy into them preserves the
   index, so a caller that copies into the slot can still conceal it at the
   type afterwards. `uint32_t_reveal_uninit` drops exactly that fact. *)
ghost fn uint32_t_reveal_uninit_at (a: ptr)
  requires uint32_t_pts_to_uninit a
  ensures  exists* b e. mem_pts_to_at a 1.0R b e
             ** pure (len b == SZ.v uint32_t_sizeof /\ aligned a uint32_t_alignof
                      /\ ET.elen e == len b /\ uint32_t_etype_ok e)


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

let ptr_sizeof : SZ.t = 8sz
let ptr_alignof : SZ.t = 8sz
let ptr_ctype : ET.ctype = ET.TScalar ET.SPtr

(* The effective-type side condition a `ptr` object's storage has to meet,
   under the name every type publishes so that a struct or union containing
   one can state its own condition without knowing what kind of type it is. *)
let ptr_etype_ok (e: ET.etypes) : prop = ET.read_ok e ptr_ctype /\ ET.allocated e

let ptr_etype_ok_none ()
  : Lemma (ptr_etype_ok (ET.etypes_none (SZ.v ptr_sizeof)))
  = ()

let ptr_etype_ok_untyped (e: ET.etypes)
  : Lemma (requires ET.untyped e /\ ET.elen e == SZ.v ptr_sizeof)
          (ensures  ptr_etype_ok e)
  = ET.untyped_read_ok e ptr_ctype; ET.allocated_untyped e

(* Storage that a store at this type has just produced meets its condition.
   This is where a union member switch lands. *)
let ptr_etype_ok_read_ok_all (_: unit)
  : Lemma (forall (e: ET.etypes). ET.read_ok e ptr_ctype /\ ET.allocated e
                             /\ ET.elen e == SZ.v ptr_sizeof ==> ptr_etype_ok e)
  = ()

(* The same, quantified: an array of this type needs it under a binder. *)
let ptr_etype_ok_untyped_all (_: unit)
  : Lemma (forall (e: ET.etypes). ET.untyped e /\ ET.elen e == SZ.v ptr_sizeof ==> ptr_etype_ok e)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires ptr_etype_ok_untyped)


let ptr_repr (a: ptr) (b: bytes) : prop =
  b == encode (SZ.v ptr_sizeof) (prov_of a) (addr_of a)

val ptr_pts_to ([@@@mkey] dest: ptr) (p: perm) (a: ptr) : slprop


val ptr_repr_len (a: ptr) (b: bytes)
  : Lemma (requires ptr_repr a b)
          (ensures  len b == SZ.v ptr_sizeof /\ initialized b /\
                    has_prov (prov_of a) b)


val ptr_repr_injective (a1 a2: ptr) (b: bytes)
  : Lemma (requires ptr_repr a1 b /\ ptr_repr a2 b)
          (ensures  a1 == a2)


(* Writing an integer over a stored pointer strips the provenance of the bytes
   it covers, and no pointer derived from an allocation is represented by
   provenance-free bytes. So the only pointer still recoverable from those bytes
   is one with the empty provenance, which cannot be dereferenced. *)
val ptr_repr_no_prov (a: ptr) (b: bytes)
  : Lemma (requires ptr_repr a b /\ no_prov b)
          (ensures  prov_of a == None)


ghost fn ptr_pts_to_not_null (dest: ptr) (#p: perm) (#a: ptr)
  preserves ptr_pts_to dest p a
  ensures   pure (not (is_null dest) /\ Some? (prov_of dest))


[@@allow_ambiguous]
ghost fn ptr_agree (dest: ptr) (#p1 #p2: perm) (#a1 #a2: ptr)
  preserves ptr_pts_to dest p1 a1
  preserves ptr_pts_to dest p2 a2
  ensures   pure (a1 == a2)


ghost fn ptr_share (dest: ptr) (#p: perm) (#a: ptr)
  requires ptr_pts_to dest p a
  ensures  ptr_pts_to dest (p /. 2.0R) a ** ptr_pts_to dest (p /. 2.0R) a


[@@allow_ambiguous]
ghost fn ptr_gather (dest: ptr) (#p1 #p2: perm) (#a1 #a2: ptr)
  requires ptr_pts_to dest p1 a1 ** ptr_pts_to dest p2 a2
  ensures  ptr_pts_to dest (p1 +. p2) a1 ** pure (a1 == a2)


ghost fn ptr_reveal (dest: ptr) (#p: perm) (#a: ptr)
  requires ptr_pts_to dest p a
  ensures  exists* b e. mem_pts_to_at dest p b e
             ** pure (ptr_repr a b /\ aligned dest ptr_alignof
                      /\ ET.elen e == len b /\ ptr_etype_ok e)


ghost fn ptr_conceal (dest: ptr) (#p: perm) (#b: bytes) (#e: ET.etypes) (#a: ptr)
  requires mem_pts_to_at dest p b e
  requires pure (ptr_repr a b)
  requires pure (aligned dest ptr_alignof)
  requires pure (ET.elen e == len b /\ ptr_etype_ok e)
  ensures  ptr_pts_to dest p a


(* A pointer-typed local, before anything has been stored in it. This is the
   same `_pts_to_uninit`/`_forget` pair every scalar type has; it exists so the
   translator can allocate and release a local without a case for pointers. *)
val ptr_pts_to_uninit ([@@@mkey] dest: ptr) : slprop


ghost fn ptr_forget (dest: ptr) (#a: ptr)
  requires ptr_pts_to dest 1.0R a
  ensures  ptr_pts_to_uninit dest


ghost fn ptr_claim_uninit (dest: ptr) (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at dest 1.0R b e
  requires pure (len b == SZ.v ptr_sizeof /\ aligned dest ptr_alignof)
  requires pure (ET.elen e == len b /\ ptr_etype_ok e)
  ensures  ptr_pts_to_uninit dest


ghost fn ptr_reveal_uninit (dest: ptr)
  requires ptr_pts_to_uninit dest
  ensures  exists* b. mem_pts_to dest 1.0R b ** pure (len b == SZ.v ptr_sizeof /\ aligned dest ptr_alignof)

(* The same, keeping the effective-type index. The bytes a stack allocation
   hands out already meet the type's condition -- that is what
   `ptr_pts_to_uninit` says -- and a byte-level copy into them preserves the
   index, so a caller that copies into the slot can still conceal it at the
   type afterwards. `ptr_reveal_uninit` drops exactly that fact. *)
ghost fn ptr_reveal_uninit_at (a: ptr)
  requires ptr_pts_to_uninit a
  ensures  exists* b e. mem_pts_to_at a 1.0R b e
             ** pure (len b == SZ.v ptr_sizeof /\ aligned a ptr_alignof
                      /\ ET.elen e == len b /\ ptr_etype_ok e)

(* ---------------------------------------------------------------------------
   Elements of an array

   `array_focus` hands back an `elem_pts_to t_repr ect`, which is the generic
   "there exist bytes representing this value" form. Every scalar type has its
   own points-to predicate instead, so each one gets a pair of ghost functions
   trading between the two. They are what makes an emitted subscript short: the
   value stays implicit throughout, so PAL never has to name `Seq.index xs i`.
   --------------------------------------------------------------------------- *)

ghost fn uint8_t_of_elem (a: ptr) (#p: perm) (#x: U8.t)
  requires elem_pts_to uint8_t_repr uint8_t_etype_ok a p x
  requires pure (aligned a uint8_t_alignof)
  ensures  uint8_t_pts_to a p x


ghost fn uint8_t_to_elem (a: ptr) (#p: perm) (#x: U8.t)
  requires uint8_t_pts_to a p x
  ensures  elem_pts_to uint8_t_repr uint8_t_etype_ok a p x
  ensures  pure (aligned a uint8_t_alignof)


ghost fn uint32_t_of_elem (a: ptr) (#p: perm) (#x: U32.t)
  requires elem_pts_to uint32_t_repr uint32_t_etype_ok a p x
  requires pure (aligned a uint32_t_alignof)
  ensures  uint32_t_pts_to a p x


ghost fn uint32_t_to_elem (a: ptr) (#p: perm) (#x: U32.t)
  requires uint32_t_pts_to a p x
  ensures  elem_pts_to uint32_t_repr uint32_t_etype_ok a p x
  ensures  pure (aligned a uint32_t_alignof)


ghost fn ptr_of_elem (a: ptr) (#p: perm) (#x: ptr)
  requires elem_pts_to ptr_repr ptr_etype_ok a p x
  requires pure (aligned a ptr_alignof)
  ensures  ptr_pts_to a p x


ghost fn ptr_to_elem (a: ptr) (#p: perm) (#x: ptr)
  requires ptr_pts_to a p x
  ensures  elem_pts_to ptr_repr ptr_etype_ok a p x
  ensures  pure (aligned a ptr_alignof)



(* ---------------------------------------------------------------------------
   GNU `a ?: b`, at each integer type.

   `a` when it is nonzero and `b` otherwise. The left operand is evaluated
   once, which is the whole reason the operator exists; PAL binds it before
   applying one of these, so the duplication below the `if` is in the
   specification only.
   --------------------------------------------------------------------------- *)
unfold let elvis_int8 (a b: FStar.Int8.t) : FStar.Int8.t = if a = 0y then b else a
unfold let elvis_int16 (a b: FStar.Int16.t) : FStar.Int16.t = if a = 0s then b else a
unfold let elvis_int32 (a b: FStar.Int32.t) : FStar.Int32.t = if a = 0l then b else a
unfold let elvis_int64 (a b: FStar.Int64.t) : FStar.Int64.t = if a = 0L then b else a
unfold let elvis_uint8 (a b: FStar.UInt8.t) : FStar.UInt8.t = if a = 0uy then b else a
unfold let elvis_uint16 (a b: FStar.UInt16.t) : FStar.UInt16.t = if a = 0us then b else a
unfold let elvis_uint32 (a b: FStar.UInt32.t) : FStar.UInt32.t = if a = 0ul then b else a
unfold let elvis_uint64 (a b: FStar.UInt64.t) : FStar.UInt64.t = if a = 0uL then b else a
unfold let elvis_size_t (a b: SZ.t) : SZ.t = if a = 0sz then b else a
