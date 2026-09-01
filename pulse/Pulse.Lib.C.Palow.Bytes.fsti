module Pulse.Lib.C.Palow.Bytes

(* ---------------------------------------------------------------------------
   Palow layer 0: the representation of memory contents.

   A byte is a *value* (absent when the byte is uninitialized) together with a
   *provenance* (absent when the byte was not written through a pointer). See
   `palow.md` for the design rationale; the short version is that we follow
   PNVI-ae-udi, so a pointer stored to memory has to keep its allocation
   identity, which means provenance necessarily lives in the bytes rather than
   only on `ptr`.

   This module is pure: nothing here mentions `slprop`. The separation-logic
   ownership of a byte range is `Pulse.Lib.C.Palow.mem_pts_to`.
   --------------------------------------------------------------------------- *)

module Seq = FStar.Seq
module U8 = FStar.UInt8

(* The identity of a single allocation (one `malloc`, one object with automatic
   or static storage duration). Kept abstract: clients may compare allocation
   ids but must not depend on how they are generated. *)
val alloc_id : eqtype

(* `None` is the *empty provenance*: a byte that was not written through a
   pointer, e.g. one written by an integer store. *)
type prov = option alloc_id

type byte = {
  value: option U8.t;  (* None = uninitialized *)
  prov:  prov;
}

type bytes = Seq.seq byte

let len (b: bytes) : nat = Seq.length b

let get (b: bytes) (i: nat { i < len b }) : byte = Seq.index b i

(* ---------------------------------------------------------------------------
   Uninitialized storage
   --------------------------------------------------------------------------- *)

let uninit_byte : byte = { value = None; prov = None }

let uninit (n: nat) : b:bytes { len b == n } = Seq.create n uninit_byte

(* All-bytes-zero, with no provenance: the contents `calloc` produces. Note that
   this is *not* the same as a null pointer's representation in general, which is
   why `calloc` does not entitle a client to read the storage back as a pointer. *)
let zero_byte : byte = { value = Some 0uy; prov = None }

let zeroed (n: nat) : b:bytes { len b == n } = Seq.create n zero_byte

(* ---------------------------------------------------------------------------
   Pointwise predicates
   --------------------------------------------------------------------------- *)

let initialized (b: bytes) : prop =
  forall (i: nat). i < len b ==> Some? (get b i).value

(* All bytes carry provenance `p`. Used to state that the bytes of a stored
   pointer all agree on its allocation, and (with `p == None`) that the bytes of
   an integer carry no provenance. *)
let has_prov (p: prov) (b: bytes) : prop =
  forall (i: nat). i < len b ==> (get b i).prov == p

let no_prov (b: bytes) : prop = has_prov None b

(* Erase provenance without touching values: what an integer store does to the
   bytes it covers. *)
let strip_prov (b: bytes) : b':bytes { len b' == len b } =
  Seq.init (len b) (fun i -> { value = (get b i).value; prov = None })

let strip_prov_index (b: bytes) (i: nat)
  : Lemma (requires i < len b)
          (ensures  get (strip_prov b) i == ({ value = (get b i).value; prov = None }))
          [SMTPat (get (strip_prov b) i)]
  = ()

let strip_prov_no_prov (b: bytes)
  : Lemma (no_prov (strip_prov b))
          [SMTPat (strip_prov b)]
  = ()

(* ---------------------------------------------------------------------------
   Splitting and joining, mirroring `mem_split` / `mem_join`
   --------------------------------------------------------------------------- *)

let slice (b: bytes) (i: nat) (j: nat { i <= j /\ j <= len b })
  : b':bytes { len b' == j - i }
  = Seq.slice b i j

let append (b1 b2: bytes) : b:bytes { len b == len b1 + len b2 } =
  Seq.append b1 b2

let slice_append (b: bytes) (i: nat { i <= len b })
  : Lemma (append (slice b 0 i) (slice b i (len b)) == b)
  = Seq.lemma_eq_intro (append (slice b 0 i) (slice b i (len b))) b

let append_slice_left (b1 b2: bytes)
  : Lemma (slice (append b1 b2) 0 (len b1) == b1)
  = Seq.lemma_eq_intro (slice (append b1 b2) 0 (len b1)) b1

let append_slice_right (b1 b2: bytes)
  : Lemma (slice (append b1 b2) (len b1) (len b1 + len b2) == b2)
  = Seq.lemma_eq_intro (slice (append b1 b2) (len b1) (len b1 + len b2)) b2

(* Byte ranges are equal when they agree pointwise; the workhorse for every
   representation proof, since `*_repr` relations are stated pointwise. *)
let bytes_ext (b1 b2: bytes)
  : Lemma (requires len b1 == len b2 /\
                    (forall (i: nat). i < len b1 ==> get b1 i == get b2 i))
          (ensures  b1 == b2)
  = Seq.lemma_eq_intro b1 b2
