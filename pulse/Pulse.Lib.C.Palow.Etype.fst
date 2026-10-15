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
module M = FStar.Math.Lemmas

(* The scalar types are a closed set -- `Pulse.Lib.C.Palow.CTypes` fixes
   exactly this one -- but the aggregates are not: PAL meets a new struct,
   union or array in every translation unit, and the model cannot enumerate
   them in advance. So a `ctype` is a *tree*, with scalars at the leaves and
   each aggregate carrying its own size and the offsets of its members. The
   emitter writes one `let struct_S_ctype : ctype = TStruct "S" 8 [...]` per
   type and nothing in this module has to change.

   `SChar` stands for the character types, which C exempts from 6.5p7
   entirely; `uint8_t` is `unsigned char`, so it is `SChar` and not a distinct
   eight-bit integer. *)
type scalar =
  | SChar
  | SBool
  | SInt8 | SInt16 | SInt32 | SInt64
  | SUInt16 | SUInt32 | SUInt64
  | SFloat32 | SFloat64
  | SPtr

let scalar_size (s: scalar) : nat =
  match s with
  | SChar | SBool | SInt8 -> 1
  | SInt16 | SUInt16 -> 2
  | SInt32 | SUInt32 | SFloat32 -> 4
  | SInt64 | SUInt64 | SFloat64 | SPtr -> 8

(* An aggregate carries its tag name as well as its layout, because C's notion
   of compatible type is by tag, not by shape: two structs with identical
   layouts are still different types, and punning between them is undefined.
   A union's members all sit at offset zero, which is the whole of the union
   rule, so unions and structs share a member list and differ only in the
   constructor -- and in the constructor being different, which is what keeps
   a struct from being compatible with a union of the same shape. *)
type ctype =
  | TScalar : scalar -> ctype
  | TStruct : string -> nat -> list (nat & ctype) -> ctype
  | TUnion  : string -> nat -> list (nat & ctype) -> ctype
  | TArr    : ctype -> nat -> ctype

let tchar : ctype = TScalar SChar

let rec csize (t: ctype) : Tot nat (decreases t) =
  match t with
  | TScalar s -> scalar_size s
  | TStruct _ n _ -> n
  | TUnion _ n _ -> n
  | TArr e n -> csize e * n

(* `access_ok` recurses into members, which are not subterms of the aggregate
   in the sense F* checks automatically, so it decreases on an explicit size.
   Every aggregate is strictly bigger than its member list, and a member list
   is strictly bigger than its tail; the second component of the lexicographic
   pair handles the case of a one-member list, where the member and the list
   have the same size. *)
let rec ctype_size (t: ctype) : Tot nat (decreases t) =
  match t with
  | TScalar _ -> 1
  | TStruct _ _ ms -> 1 + members_size ms
  | TUnion _ _ ms -> 1 + members_size ms
  | TArr e _ -> 1 + ctype_size e
and members_size (ms: list (nat & ctype)) : Tot nat (decreases ms) =
  match ms with
  | [] -> 0
  | (_, m) :: r -> ctype_size m + members_size r

(* Total remainder, so that the array case does not need a well-formedness side
   condition on zero-length element types. *)
let emod (x: int) (m: nat) : int = if m = 0 then x else x % m

(* `access_ok ty off u` -- an object of type `ty` has, at byte offset `off`, a
   subobject of type `u` that may be accessed. This is the "compatible" side
   condition of 6.5p7, spelled out by cases:

   - a character type may access anything;
   - a type may access itself at offset 0;
   - an array delegates to its element type, modulo the element size, which is
     what makes `a[i]` an access to the element rather than to the array; and
   - an aggregate delegates to each member at that member's offset. For a
     union every offset is zero, so every member is accessible -- which is
     exactly the C rule that reading any member of a union object is
     permitted. Type punning through a union is legal C, and it stays legal
     here.

   It is a `bool` rather than a `prop` because the solver has to *compute* it:
   every descriptor is a closed term, so each instance reduces to `true` or
   `false` without the solver having to reason about the recursion. That also
   makes it usable in the `if` of `store_entry` below.

   An access also has to *fit*: it covers `csize u` bytes starting at `off`,
   and those have to be inside the object. Without that bound the character
   rule would licence a byte access at any offset whatsoever, including
   outside the object, and `access_ok` would not compose (see
   `access_ok_trans`). *)
let rec access_ok (ty: ctype) (off: int) (u: ctype) : Tot bool (decreases %[ctype_size ty; 0]) =
  0 < csize u && 0 <= off && off + csize u <= csize ty &&
  (u = tchar ||
  (off = 0 && ty = u) ||
  (match ty with
   | TArr e n -> 0 <= off && off < csize e * n && access_ok e (emod off (csize e)) u
   | TStruct _ _ ms -> access_ok_members ms off u
   | TUnion _ _ ms -> access_ok_members ms off u
   | TScalar _ -> false))
and access_ok_members (ms: list (nat & ctype)) (off: int) (u: ctype)
  : Tot bool (decreases %[members_size ms; 1]) =
  match ms with
  | [] -> false
  | (o, m) :: r -> access_ok m (off - o) u || access_ok_members r off u

(* Stepping an offset within an element never carries out of it, because an
   access fits inside the object it is an access to. *)
let mod_add_no_carry (d: nat) (q: pos) (off: nat)
  : Lemma (requires d % q + off < q)
          (ensures  (d + off) % q == d % q + off)
  = M.euclidean_division_definition d q;
    M.lemma_mod_plus (d % q + off) (d / q) q;
    M.small_mod (d % q + off) q

(* `access_ok` composes: if `ty` has an `s` at offset `d`, and an `s` has a
   `fld` at offset `off`, then `ty` has a `fld` at `d + off`.

   This is the load-bearing lemma of the whole design, because it is what lets
   the index stay out of the aggregate predicates. A struct's bytes are
   labelled with the *struct's* type, so reading one member is an access at a
   type the byte's label does not mention; composition is what turns "these
   bytes hold a struct S" into "these four of them may be read as a
   uint32_t". Without it, every aggregate predicate would have to carry the
   index so that field claims could be justified from it directly. *)
let rec access_ok_trans (ty: ctype) (d: int) (s: ctype) (off: int) (fld: ctype)
  : Lemma (requires access_ok ty d s /\ access_ok s off fld)
          (ensures  access_ok ty (d + off) fld)
          (decreases %[ctype_size ty; 0])
  = if s = tchar || (d = 0 && ty = s) then () else
    match ty with
    | TScalar _ -> ()
    | TArr e n ->
      access_ok_trans e (emod d (csize e)) s off fld;
      if csize e > 0 then begin
        assert (emod d (csize e) + csize s <= csize e);
        assert (off + csize fld <= csize s);
        mod_add_no_carry d (csize e) off
      end
    | TStruct _ _ ms -> access_ok_trans_members ms d s off fld
    | TUnion _ _ ms -> access_ok_trans_members ms d s off fld
and access_ok_trans_members (ms: list (nat & ctype)) (d: int) (s: ctype) (off: int) (fld: ctype)
  : Lemma (requires access_ok_members ms d s /\ access_ok s off fld)
          (ensures  access_ok_members ms (d + off) fld)
          (decreases %[members_size ms; 1])
  = match ms with
    | [] -> ()
    | (o, m) :: r ->
      if access_ok m (d - o) s then access_ok_trans m (d - o) s off fld
      else access_ok_trans_members r d s off fld

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

(* A byte's offset within its object is an offset *into* that object. Every
   index this module builds satisfies this, and `store_etypes` preserves it;
   it is stated separately because `etypes` is a plain sequence. *)
let etypes_wf (e: etypes) : prop =
  forall (k: nat). k < elen e ==>
    (match eget e k with None -> True | Some en -> en.off < csize en.ty)

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
     | Some en -> b2t (access_ok en.ty (en.off - k) u)))

(* A byte is relabelled only if its current type does not already license the
   store. That condition is what keeps the index from being *too* fine: writing
   an `int` through a pointer to the first member of a `struct a` must not turn
   those four bytes into a standalone `int` object and so destroy the enclosing
   struct, and it does not, because `access_ok struct_a_ctype 0 int32_t_ctype`
   already holds. Only a store the current type does *not* license -- writing
   a `struct b` over storage that held a `struct a` -- moves the index, which
   is exactly the case 6.5p6 is about. *)
let store_entry (en: option etype_entry) (u: ctype) (k: nat) : option etype_entry =
  match en with
  | Some e0 ->
    if e0.fixed || access_ok e0.ty (e0.off - k) u then Some e0
    else Some ({ ty = u; off = k; fixed = false })
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

   The aggregates the examples in `Pulse.Lib.C.Palow.Aggregate` and
   `Pulse.Lib.C.Palow.Union` use, written as descriptors. These stand in for
   what PAL emits; nothing below knows they are the only ones.
   --------------------------------------------------------------------------- *)

let ct_u32 : ctype = TScalar SUInt32
let ct_ptr : ctype = TScalar SPtr

(* struct S { uint32_t f; uint8_t g; }, size 8 *)
let ct_S : ctype = TStruct "S" 8 [(0, ct_u32); (4, tchar)]

(* struct T { uint32_t y; uint32_t z; } *)
let ct_T : ctype = TStruct "T" 8 [(0, ct_u32); (4, ct_u32)]

(* union U { uint32_t x; struct T t; } -- every member at offset zero *)
let ct_U : ctype = TUnion "U" 8 [(0, ct_u32); (0, ct_T)]

(* Character types are exempt: this is why `memcpy` and byte-wise inspection
   never need to know an object's type. *)
let read_char_ok (e: etypes)
  : Lemma (requires elen e == 1 /\ etypes_wf e)
          (ensures  read_ok e tchar)
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
  : Lemma (read_ok (Seq.slice (etypes_of ct_U true) 0 4) ct_u32)
  = ()

let union_read_t_z_ok ()
  : Lemma (read_ok (Seq.slice (etypes_of ct_U true) 4 8) ct_u32)
  = ()

(* A struct member is readable at its own offset, and the descriptor is
   generated, so this is the shape every field access has. *)
let struct_member_read_ok ()
  : Lemma (read_ok (Seq.slice (etypes_of ct_T true) 4 8) ct_u32)
  = ()

(* But a struct is not compatible with a union of the same shape, nor with
   another struct of the same layout: C compares tags, not bytes. *)
let struct_not_union ()
  : Lemma (~(access_ok ct_T 0 ct_U))
  = ()

(* The rule that actually does work: allocated storage whose last store was an
   integer cannot then be read as a pointer. Under a model without effective
   types this program verifies; clang is entitled to miscompile it. *)
let no_int_to_ptr_pun ()
  : Lemma (~(read_ok (Seq.append (store_etypes (etypes_none 4) ct_u32)
                                 (store_etypes (etypes_none 4) ct_u32))
                     ct_ptr))
  = assert (eget (Seq.append (store_etypes (etypes_none 4) ct_u32)
                             (store_etypes (etypes_none 4) ct_u32)) 0
            == Some ({ ty = ct_u32; off = 0; fixed = false }))

(* ...but the same storage *is* readable as a pointer if that is what was
   stored into it, which is what keeps `Pulse.Lib.C.Palow.Provenance` alive
   once the rules are switched on. *)
let ptr_store_read_ok ()
  : Lemma (read_ok (store_etypes (etypes_none 8) ct_ptr) ct_ptr)
  = ()

(* An array of `uint32_t` is readable element by element, at every element. *)
let array_elem_read_ok (n: nat) (i: nat { i < n })
  : Lemma (read_ok (Seq.slice (etypes_of (TArr ct_u32 n) true) (4 * i) (4 * i + 4)) ct_u32)
  = assert (forall (k: nat). k < 4 ==> emod (4 * i + k - k) 4 == 0)

(* A store through a member's own type does not disturb the object it is a
   member of: this is the "is the index too fine?" question, and the answer is
   no. Writing a `uint32_t` over the first member of an allocated `struct T`
   leaves the whole index alone, so the struct can still be read as a struct
   afterwards. *)
let member_store_keeps_object ()
  : Lemma (store_etypes (Seq.slice (etypes_of ct_T false) 0 4) ct_u32
           == Seq.slice (etypes_of ct_T false) 0 4)
  = Seq.lemma_eq_intro (store_etypes (Seq.slice (etypes_of ct_T false) 0 4) ct_u32)
                       (Seq.slice (etypes_of ct_T false) 0 4)

(* But a store the current type does *not* license does move the index, which
   is what makes allocated storage reusable at another type -- legal C, and the
   reason the retype step has to exist at all. It takes the whole object: the
   permission required is full permission over all `csize u` bytes. *)
let retype_allocated ()
  : Lemma (store_etypes (etypes_of ct_T false) ct_S == etypes_of ct_S false)
  = assert (~(access_ok ct_T 0 ct_S));
    Seq.lemma_eq_intro (store_etypes (etypes_of ct_T false) ct_S) (etypes_of ct_S false)

(* And a *declared* object is never retyped, however the store is made. *)
let retype_declared ()
  : Lemma (store_etypes (etypes_of ct_T true) ct_S == etypes_of ct_T true)
  = Seq.lemma_eq_intro (store_etypes (etypes_of ct_T true) ct_S) (etypes_of ct_T true)

(* ---------------------------------------------------------------------------
   Where the index has to be visible

   These two settle how far the index has to be threaded through the typed
   layer. The first says a member claim is justified by the *enclosing
   object's* index, via `access_ok_trans` -- so a struct's byte-facing entry
   points can hand out field permissions without the field predicates ever
   naming an index. The second says the converse fails, so the index cannot be
   dropped at the aggregate boundary and reconstructed from the fields.
   --------------------------------------------------------------------------- *)

(* Downward: an index that licenses a read at `s` licenses a read of `s`'s
   member `fld` over exactly that member's bytes. *)
let read_ok_slice (e: etypes) (s: ctype) (off: nat) (fld: ctype)
  : Lemma (requires read_ok e s /\ access_ok s off fld /\ off + csize fld <= elen e)
          (ensures  read_ok (Seq.slice e off (off + csize fld)) fld)
  = let e' = Seq.slice e off (off + csize fld) in
    let aux (k: nat { k < elen e' })
      : Lemma (match eget e' k with
               | None -> True
               | Some en -> b2t (access_ok en.ty (en.off - k) fld))
      = match eget e' k with
        | None -> ()
        | Some en -> access_ok_trans en.ty (en.off - (off + k)) s off fld
    in
    FStar.Classical.forall_intro aux

(* Upward: it does not come back. Two standalone `uint32_t` objects side by
   side each licence a `uint32_t` read, and together they occupy exactly the
   bytes of a `struct T { uint32_t y, z; }` -- but they are not one, and no
   amount of field-level information says otherwise. So an aggregate's index
   is strictly more than the conjunction of its fields' indices, and the
   byte-facing entry points that build an aggregate out of bytes have to be
   given it. *)
let fields_dont_make_a_struct ()
  : Lemma (let e = Seq.append (etypes_of ct_u32 false) (etypes_of ct_u32 false) in
           read_ok (Seq.slice e 0 4) ct_u32 /\
           read_ok (Seq.slice e 4 8) ct_u32 /\
           ~(read_ok e ct_T))
  = let e = Seq.append (etypes_of ct_u32 false) (etypes_of ct_u32 false) in
    Seq.lemma_eq_intro (Seq.slice e 0 4) (etypes_of ct_u32 false);
    Seq.lemma_eq_intro (Seq.slice e 4 8) (etypes_of ct_u32 false);
    assert (eget e 0 == Some ({ ty = ct_u32; off = 0; fixed = false }));
    assert (~(access_ok ct_u32 0 ct_T))
