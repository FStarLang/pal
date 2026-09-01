module Pulse.Lib.C.Palow.Etype

(* ---------------------------------------------------------------------------
   Effective types (C11 6.5p6-7).

   Effective types are what license a C compiler's type-based alias analysis.
   Ignoring them is *permissive*: we would accept programs that clang may
   miscompile. Since ignoring them never blocks a proof, enforcement can be
   staged last -- but the vocabulary has to exist before layer 0 is threaded
   through the translator, because retrofitting an index onto `mem_pts_to`
   afterwards would touch every module.

   This is that vocabulary, and it is a proved module: `access_ok` and the
   store rule are ordinary definitions, and the facts we care about are
   theorems about them. Two are worth stating up front, because they are the
   ones that decide whether the rules are usable at all:

   - reading a `uint32_t` out of a `union U` object is allowed, at both member
     offsets, which is what makes acceptance test 2 survive the addition of
     effective types (`union_read_x_ok`, `union_read_t_z_ok`); and
   - reading a pointer out of storage whose last store was an integer is *not*
     allowed (`no_int_to_ptr_pun`), which is the rule actually doing work.

   As everywhere else in Palow, `ctype` is a closed enumeration standing in for
   what PAL would generate per translation unit, instantiated here at exactly
   the types the rest of the model uses. Nothing depends on the enumeration
   being open-ended: `access_ok` is defined by cases, which is precisely the
   shape a code generator emits.
   --------------------------------------------------------------------------- *)

open Pulse

module Seq = FStar.Seq

(* The types PAL would generate a descriptor for. `TStructS`, `TStructT` and
   `TUnionU` mirror the aggregates in `Pulse.Lib.C.Palow.Aggregate` and
   `Pulse.Lib.C.Palow.Union`; `TUChar` stands for the character types, which
   C exempts from the rules entirely. *)
type ctype =
  | TUChar
  | TUInt32
  | TPtr
  | TStructS                    (* struct S { uint32_t f; uint8_t g; }, size 8 *)
  | TStructT                    (* struct T { uint32_t y; uint32_t z; }        *)
  | TUnionU                     (* union U  { uint32_t x; struct T t; }        *)
  | TArr : ctype -> nat -> ctype

let rec csize (t: ctype) : Tot nat (decreases t) =
  match t with
  | TUChar -> 1
  | TUInt32 -> 4
  | TPtr -> 8
  | TStructS -> 8
  | TStructT -> 8
  | TUnionU -> 8
  | TArr e n -> csize e * n

(* `access_ok` recurses into members, which are not structurally smaller than
   the aggregate, so it decreases on an explicit rank instead. The rank is just
   "how deeply nested is this type": every member of an aggregate has a
   strictly smaller one. *)
let rec crank (t: ctype) : Tot nat (decreases t) =
  match t with
  | TUChar | TUInt32 | TPtr -> 0
  | TStructS | TStructT -> 1
  | TUnionU -> 2
  | TArr e _ -> crank e + 1

(* Total remainder, so that the array case does not need a well-formedness side
   condition on zero-length element types. *)
let emod (x: int) (m: nat) : int = if m = 0 then x else x % m

(* `access_ok ty off u` -- an object of type `ty` has, at byte offset `off`, a
   subobject of type `u` that may be accessed. This is the "compatible" side
   condition of 6.5p7, spelled out by cases:

   - a character type may access anything;
   - a type may access itself at offset 0;
   - an array delegates to its element type, modulo the element size, which is
     what makes `a[i]` an access to the element rather than to the array;
   - a struct delegates to each member at that member's offset; and
   - a union delegates to *every* member at offset 0, which is exactly the
     C rule that reading any member of a union object is permitted. Type
     punning through a union is legal C, and it stays legal here. *)
let rec access_ok (ty: ctype) (off: int) (u: ctype) : Tot prop (decreases crank ty) =
  u == TUChar \/
  (off == 0 /\ ty == u) \/
  (match ty with
   | TArr e n -> 0 <= off /\ off < csize e * n /\ access_ok e (emod off (csize e)) u
   | TStructS -> access_ok TUInt32 off u \/ access_ok TUChar (off - 4) u
   | TStructT -> access_ok TUInt32 off u \/ access_ok TUInt32 (off - 4) u
   | TUnionU -> access_ok TUInt32 off u \/ access_ok TStructT off u
   | _ -> False)

(* One entry per byte: which object this byte belongs to, and which byte of it
   this is. `fixed` distinguishes a declared object, whose type is settled for
   its whole lifetime, from allocated storage, which takes its effective type
   from the last store. `None` is storage that has no effective type yet. *)
type etype_entry = {
  ty: ctype;
  off: nat;
  fixed: bool;
}

type etypes = Seq.seq (option etype_entry)

let elen (e: etypes) : nat = Seq.length e
let eget (e: etypes) (i: nat { i < elen e }) : option etype_entry = Seq.index e i

(* Freshly allocated storage: no effective type anywhere. *)
let etypes_none (n: nat) : e:etypes { elen e == n } = Seq.create n None

(* A declared (`fixed`) or stored-into object of type `t` occupying its own
   bytes, each byte tagged with its offset within the object. *)
let etypes_of (t: ctype) (fx: bool) : e:etypes { elen e == csize t } =
  Seq.init (csize t) (fun k -> Some ({ ty = t; off = k; fixed = fx }))

(* An access of type `u` covering exactly the bytes described by `e`. Byte `k`
   of the access is byte `en.off` of its object, so the object's subobject of
   type `u` starts at `en.off - k`; requiring `access_ok` at that offset is
   what forces all the covered bytes to come from the same subobject. *)
let read_ok (e: etypes) (u: ctype) : prop =
  elen e == csize u /\
  (forall (k: nat). k < elen e ==>
    (match eget e k with
     | None -> True
     | Some en -> access_ok en.ty (en.off - k) u))

let store_entry (en: option etype_entry) (u: ctype) (k: nat) : option etype_entry =
  match en with
  | Some e0 -> if e0.fixed then Some e0 else Some ({ ty = u; off = k; fixed = false })
  | None -> Some ({ ty = u; off = k; fixed = false })

(* A store at type `u` gives allocated storage that effective type, and leaves
   declared objects alone. Character stores are simply not routed through here:
   6.5p6 says they do not change the effective type. *)
let store_etypes (e: etypes) (u: ctype { elen e == csize u }) : e':etypes { elen e' == elen e } =
  Seq.init (elen e) (fun k -> store_entry (eget e k) u k)

(* `memcpy` transports the entries along with the bytes, matching the C rule
   that a byte-copied object inherits the source object's effective type. That
   is just "the destination index becomes the source index", so there is no
   separate definition -- it is the same transport that gives `memcpy` its byte
   spec in `Pulse.Lib.C.Palow.Machine`. *)

(* ---------------------------------------------------------------------------
   Theorems
   --------------------------------------------------------------------------- *)

(* Character types are exempt: this is why `memcpy` and byte-wise inspection
   never need to know an object's type. *)
let read_char_ok (e: etypes)
  : Lemma (requires elen e == 1)
          (ensures  read_ok e TUChar)
  = ()

(* Storing into untyped storage gives it that effective type, and it is then
   readable at that type. This is the `malloc` case. *)
let store_none_read_ok (u: ctype)
  : Lemma (read_ok (store_etypes (etypes_none (csize u)) u) u)
  = ()

(* A declared object keeps its type: storing at a different type through a
   pointer does not relabel it. *)
let store_fixed_stable (t: ctype) (u: ctype { csize u == csize t })
  : Lemma (store_etypes (etypes_of t true) u == etypes_of t true)
  = Seq.lemma_eq_intro (store_etypes (etypes_of t true) u) (etypes_of t true)

(* Acceptance test 2 under effective types: a `union U` object may be read
   through `.x`, and through `.t.y` and `.t.z`, all at `uint32_t`. The `.z`
   case is the interesting one -- the bytes are at offset 4 of the union, so
   the rule has to go through the `struct T` member to reach a `uint32_t` at
   its offset 0. *)
let union_read_x_ok ()
  : Lemma (read_ok (Seq.slice (etypes_of TUnionU true) 0 4) TUInt32)
  = ()

let union_read_t_z_ok ()
  : Lemma (read_ok (Seq.slice (etypes_of TUnionU true) 4 8) TUInt32)
  = ()

(* The rule that actually does work: allocated storage whose last store was an
   integer cannot then be read as a pointer. Under a model without effective
   types this program verifies; clang is entitled to miscompile it. *)
let no_int_to_ptr_pun ()
  : Lemma (~(read_ok (Seq.append (store_etypes (etypes_none 4) TUInt32)
                                 (store_etypes (etypes_none 4) TUInt32))
                     TPtr))
  = assert (eget (Seq.append (store_etypes (etypes_none 4) TUInt32)
                             (store_etypes (etypes_none 4) TUInt32)) 0
            == Some ({ ty = TUInt32; off = 0; fixed = false }))

(* ...but the same storage *is* readable as a pointer if that is what was
   stored into it, which is what keeps `Pulse.Lib.C.Palow.Provenance` alive
   once the rules are switched on. *)
let ptr_store_read_ok ()
  : Lemma (read_ok (store_etypes (etypes_none 8) TPtr) TPtr)
  = ()

(* An array of `uint32_t` is readable element by element, at every element. *)
let array_elem_read_ok (n: nat) (i: nat { i < n })
  : Lemma (read_ok (Seq.slice (etypes_of (TArr TUInt32 n) true) (4 * i) (4 * i + 4)) TUInt32)
  = assert (forall (k: nat). k < 4 ==> emod (4 * i + k - k) 4 == 0)
