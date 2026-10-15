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

(* 6.5p7 bullet 3: "the signed or unsigned type corresponding to the effective
   type of the object". Reading an `int` object through `unsigned int *` is
   explicitly permitted, so the two have to be interchangeable in `access_ok`.

   `SChar` is its own counterpart, and so is everything else that has none:
   `int8_t` and `uint8_t` are both character types and are both `SChar`
   already, so there is no eight-bit pair to relate, and the floating and
   pointer types have no signedness to flip. Identity is the right answer for
   all of them -- the disjunct it feeds is then simply `ty = u`, which is
   already there. *)
let counterpart (s: scalar) : scalar =
  match s with
  | SInt16 -> SUInt16 | SUInt16 -> SInt16
  | SInt32 -> SUInt32 | SUInt32 -> SInt32
  | SInt64 -> SUInt64 | SUInt64 -> SInt64
  | s -> s

let counterpart_involutive (s: scalar)
  : Lemma (counterpart (counterpart s) == s)
          [SMTPat (counterpart (counterpart s))]
  = ()

(* A type and its counterpart have the same width, which is what lets the
   disjunct be added to `access_ok` without disturbing the bounds check. *)
let counterpart_size (s: scalar)
  : Lemma (scalar_size (counterpart s) == scalar_size s)
          [SMTPat (scalar_size (counterpart s))]
  = ()

(* The relation lifted to `ctype`, so that `access_ok` can test it in one
   place. `counterpart_involutive` is what makes it symmetric. *)
let counterpart_ok (ty: ctype) (u: ctype) : bool =
  match ty, u with
  | TScalar a, TScalar b -> b = counterpart a
  | _ -> false

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
   - a type may access itself at offset 0, and so may the signed or unsigned
     type corresponding to it (6.5p7 bullet 3, `counterpart_ok`);
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
  (off = 0 && counterpart_ok ty u) ||
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
  = if s = tchar || (d = 0 && ty = s) || (d = 0 && counterpart_ok ty s) then () else
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

(* The length of a slice, with a trigger on `elen` rather than on
   `Seq.length`. Every condition here is written in terms of `elen`, so
   without this the solver has to unfold the abbreviation before the sequence
   library's own lemma can fire -- which it does happily in a small goal and
   not at all in a proof that carves a sixty-nine-field struct apart. *)
let elen_slice (e: etypes) (i: nat) (j: nat)
  : Lemma (requires i <= j /\ j <= elen e)
          (ensures  elen (Seq.slice e i j) == j - i)
          [SMTPat (elen (Seq.slice e i j))]
  = ()

(* A byte's offset within its object is an offset *into* that object. Every
   index this module builds satisfies this, and `store_etypes` preserves it;
   it is stated separately because `etypes` is a plain sequence. *)
let etypes_wf (e: etypes) : prop =
  forall (k: nat). k < elen e ==>
    (match eget e k with None -> True | Some en -> en.off < csize en.ty)

(* Freshly allocated storage: no effective type anywhere. *)
let etypes_none (n: nat) : e:etypes { elen e == n } = Seq.create n None

(* Carving a range twice is carving it once. Stated with a pattern so that the
   nested slices a struct's field-by-field carve produces collapse to the flat
   slice its side condition is written with, without a hint per field. *)
let etypes_slice_slice (e: etypes) (i j k l: nat)
  : Lemma (requires i <= j /\ j <= elen e /\ k <= l /\ l <= j - i)
          (ensures  Seq.slice (Seq.slice e i j) k l == Seq.slice e (i + k) (i + l))
          [SMTPat (Seq.slice (Seq.slice e i j) k l)]
  = Seq.slice_slice e i j k l

(* Untyped storage stays untyped when it is cut up. Used wherever a block is
   handed out piecewise -- `mem_split_at` on `malloc`ed or pool storage. *)
let etypes_none_slice (n: nat) (i: nat) (j: nat)
  : Lemma (requires i <= j /\ j <= n)
          (ensures  Seq.slice (etypes_none n) i j == etypes_none (j - i))
          [SMTPat (Seq.slice (etypes_none n) i j)]
  = Seq.lemma_eq_intro (Seq.slice (etypes_none n) i j) (etypes_none (j - i))

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

(* A subobject of a readable object is readable at its own type. This is the
   bridge from the array layer, which states an element's condition as
   `read_ok e ect`, to the struct layer, which states a containing type's
   condition field by field: a struct that is readable as a whole is readable
   at each of its fields, by `access_ok_trans`. *)
let read_ok_sub (e: etypes) (s: ctype) (off: nat) (fld: ctype)
  : Lemma (requires read_ok e s /\ access_ok s off fld /\ off + csize fld <= elen e)
          (ensures  read_ok (Seq.slice e off (off + csize fld)) fld)
  = let e' = Seq.slice e off (off + csize fld) in
    let aux (k: nat)
      : Lemma (k < elen e' ==>
               (match eget e' k with
                | None -> True
                | Some en -> b2t (access_ok en.ty (en.off - k) fld)))
      = if k < elen e' then
          match eget e' k with
          | None -> ()
          | Some en -> access_ok_trans en.ty (en.off - (off + k)) s off fld
    in
    FStar.Classical.forall_intro aux

(* Storage that has no effective type at all. `read_ok` is satisfied by it at
   every type, which is what makes it the right description of two things C
   treats alike: the result of `malloc`, and the storage of a *union*.

   For the union that is not a shortcut. 6.5.2.3p3 and its footnote permit
   reading any member of a union object, whichever one was last stored, so a
   union's bytes have to admit a read at every member's type. Saying they carry
   no effective type says exactly that, and -- unlike a conjunction of
   `read_ok`s, one per member -- it splits and rejoins, which is what a member
   focus and unfocus need. *)
let untyped (e: etypes) : prop =
  forall (k: nat). k < elen e ==> eget e k == None

(* Storage that may be re-typed: every byte either has no effective type yet
   or belongs to an allocated object, which 6.5p6 lets a store relabel. The
   complement is a *declared* object, whose declared type is its effective
   type for good.

   This is the half of 6.5p6 that `read_ok` does not record. `read_ok` says
   what may be read out of a byte; `allocated` says whether a store may change
   that, and a cross-member union write needs the second. Unlike `read_ok` it
   is pointwise and offset-free, so it splits and rejoins by construction. *)
let allocated (e: etypes) : prop =
  forall (k: nat). k < elen e ==>
    (match eget e k with None -> True | Some en -> b2t (not en.fixed))

let allocated_slice (e: etypes) (i j: nat)
  : Lemma (requires allocated e /\ i <= j /\ j <= elen e)
          (ensures  allocated (Seq.slice e i j))
          [SMTPat (allocated (Seq.slice e i j))]
  = ()

let allocated_append (e1 e2: etypes)
  : Lemma (requires allocated e1 /\ allocated e2)
          (ensures  allocated (Seq.append e1 e2))
          [SMTPat (allocated (Seq.append e1 e2))]
  = ()

let allocated_untyped (e: etypes)
  : Lemma (requires untyped e) (ensures allocated e)
          [SMTPat (allocated e); SMTPat (untyped e)]
  = ()

let allocated_none (n: nat)
  : Lemma (allocated (etypes_none n))
          [SMTPat (allocated (etypes_none n))]
  = ()

let untyped_read_ok (e: etypes) (u: ctype)
  : Lemma (requires untyped e /\ elen e == csize u)
          (ensures  read_ok e u)
  = ()

let untyped_slice (e: etypes) (i j: nat)
  : Lemma (requires untyped e /\ i <= j /\ j <= elen e)
          (ensures  untyped (Seq.slice e i j))
          [SMTPat (untyped (Seq.slice e i j))]
  = ()

let untyped_append (e1 e2: etypes)
  : Lemma (requires untyped e1 /\ untyped e2)
          (ensures  untyped (Seq.append e1 e2))
  = ()

let untyped_none (n: nat)
  : Lemma (untyped (etypes_none n))
  = ()

(* A byte is relabelled only if its current type does not already license the
   store. That condition is what keeps the index from being *too* fine: writing
   an `int` through a pointer to the first member of a `struct a` must not turn
   those four bytes into a standalone `int` object and so destroy the enclosing
   struct, and it does not, because `access_ok struct_a_ctype 0 int32_t_ctype`
   already holds. Only a store the current type does *not* license -- writing
   a `struct b` over storage that held a `struct a` -- moves the index, which
   is exactly the case 6.5p6 is about.

   A store through a character lvalue moves nothing at all. 6.5p6 installs the
   lvalue's type only "through an lvalue having a type that is not a character
   type", so writing a byte into fresh `malloc`ed storage leaves that storage
   *untyped* rather than making it a one-byte `char` object. The difference is
   not academic: without the guard, the usual idiom of clearing a buffer and
   then storing a struct into it would have to re-type every byte, and the
   `None` entries that make `calloc`ed storage readable at any type would be
   gone after the first byte-wise write.

   Carving the rule out here rather than in the emitter is deliberate. Every
   character type in the model is `TScalar SChar` -- `uint8_t`, `int8_t` and
   `char` all are -- so `u = tchar` catches all three, and a typed write can
   be emitted uniformly instead of having a special case for one type. *)
let store_entry (en: option etype_entry) (u: ctype) (k: nat) : option etype_entry =
  if u = tchar then en else
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

(* `store_etypes` says how a store *moves* the index. It does not say whether
   the store is *allowed*, and those are different questions: a store at an
   incompatible type into a declared object is undefined behaviour (6.5p7),
   not a relabelling, and `store_entry` quietly leaves such a byte alone.

   `store_ok` is the missing side condition. A byte admits a store at `u` when
   it has no effective type yet, or belongs to allocated storage -- which may
   always be re-typed -- or already licenses the access. Only the third
   disjunct is available to a declared object, which is precisely 6.5p6's "if
   the object has a declared type, that is its effective type" read as a
   restriction on stores.

   Character stores take only the third disjunct, which at `tchar` amounts to
   the byte being in bounds of the object it belongs to. That is not a
   restriction on what C permits -- a character store is always allowed -- but
   on what this lemma can conclude afterwards: since a character store moves
   nothing, the only way the bytes are readable at `tchar` after it is for
   them to have been readable at `tchar` before, and the `not fixed` disjunct
   does not say that. *)
let store_ok (e: etypes) (u: ctype) : prop =
  elen e == csize u /\
  (forall (k: nat). k < elen e ==>
    (match eget e k with
     | None -> True
     | Some en -> b2t (access_ok en.ty (en.off - k) u) \/
                  (u =!= tchar /\ b2t (not en.fixed))))

(* The load-bearing theorem for enforcement: a permitted store leaves the bytes
   readable at the type that was stored. Without it a typed write could not
   re-establish its own points-to, and every `T_write` in the generated code
   would be stuck. `store_none_read_ok` below is its all-`None` special case --
   the `malloc` one -- and is kept because it names that case. *)
let store_ok_read_ok (e: etypes) (u: ctype)
  : Lemma (requires store_ok e u)
          (ensures  read_ok (store_etypes e u) u)
  = let e' = store_etypes e u in
    let aux (k: nat { k < elen e' })
      : Lemma (match eget e' k with
               | None -> True
               | Some en -> b2t (access_ok en.ty (en.off - k) u))
      = (* Either the byte kept its entry, in which case `store_entry`'s test
           or `store_ok` says that entry licenses `u`, or it was relabelled to
           `u` at offset `k`, and `access_ok u 0 u` is immediate. *)
        assert (eget e' k == store_entry (eget e k) u k)
    in
    FStar.Classical.forall_intro aux

(* Allocated storage admits a store at any type of the right size: that is
   `store_ok`'s second disjunct, and the whole reason the flag is tracked. *)
let allocated_store_ok (e: etypes) (u: ctype)
  : Lemma (requires allocated e /\ elen e == csize u /\ ~(u == tchar))
          (ensures  store_ok e u)
  = ()

(* And a store leaves it allocated: `store_entry` either keeps an entry that
   was already not `fixed`, or writes a fresh one that is not. *)
let allocated_store_etypes (e: etypes) (u: ctype { elen e == csize u })
  : Lemma (requires allocated e) (ensures allocated (store_etypes e u))
  = let e' = store_etypes e u in
    let aux (k: nat)
      : Lemma (k < elen e' ==>
               (match eget e' k with None -> True | Some en -> b2t (not en.fixed)))
      = if k < elen e' then assert (eget e' k == store_entry (eget e k) u k)
    in
    FStar.Classical.forall_intro aux


(* `memcpy` transports the entries along with the bytes, matching the C rule
   that a byte-copied object inherits the source object's effective type.

   It is *not* plain transport, which is the trap this definition exists to
   avoid. 6.5p6's third rule applies only to "an object having no declared
   type"; copying a `double` over a declared `int` does not make it a `double`
   (case 14.1 of `test/effective_type`). So a `fixed` destination byte keeps
   its entry and only the rest follows the source -- the same asymmetry
   `store_entry` has, and for the same reason.

   The copied entry is also stripped of `fixed`. R3 gives the destination the
   source's effective *type*; it does not give it a declared type, which is a
   property of how the destination was created and not of what was written
   into it. Without the strip, `memcpy`ing a declared object into `malloc`ed
   storage would make that storage permanently un-re-typeable, and case 5.3
   followed by case 4.2 -- copy into allocated storage, then store a new type
   over it -- would stop being legal C. *)
let unfix (en: option etype_entry) : option etype_entry =
  match en with
  | Some e0 -> Some ({ e0 with fixed = false })
  | None -> None

let copy_entry (d: option etype_entry) (s: option etype_entry) : option etype_entry =
  match d with
  | Some d0 -> if d0.fixed then Some d0 else unfix s
  | None -> unfix s

let copy_etypes (dst: etypes) (src: etypes { elen src == elen dst })
  : e:etypes { elen e == elen dst } =
  Seq.init (elen dst) (fun k -> copy_entry (eget dst k) (eget src k))

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

(* ...except through a character lvalue, which installs nothing at all. This is
   the half of 6.5p6 that is easy to drop, and dropping it would break more
   than the character cases: a `memset`-then-store idiom types the storage at
   `char` on the first byte written, and the later store at the real type then
   has to re-type storage that should still have been untyped.

   Stated as an equality on the whole index rather than as a fact about
   `read_ok`, because the point is that *nothing moves*: the storage is as
   untyped after a character store as it was before, and so is still readable
   at every type. Case 6.2 of `test/_effective_type` is this theorem. *)
let store_char_identity (e: etypes { elen e == csize tchar })
  : Lemma (store_etypes e tchar == e)
  = Seq.lemma_eq_intro (store_etypes e tchar) e

(* The consequence that matters: bytes written through a character lvalue stay
   untyped, so storage filled byte-by-byte is still claimable at any type
   afterwards -- which is what makes a hand-written allocator, or a decoder
   that assembles an object from a byte buffer, legal C rather than a pun. *)
let store_char_keeps_none ()
  : Lemma (store_etypes (etypes_none 1) tchar == etypes_none 1)
  = store_char_identity (etypes_none 1)

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
   The acceptance tests, transcribed from `test/effective_type`

   One theorem per case transcribed, named after it, so that the rules are
   pinned here -- by computation, with no memory model and no translator in the
   way -- before anything depends on them. A `[DEFINED]` case becomes a
   positive theorem and a `[UB]` case a negative one, and a rule that stops
   being enforced breaks this module rather than silently widening what PAL
   accepts.

   These are the cases that bear on the rules this module states, not the whole
   corpus. Sections 19-22 are about `volatile`, `_Atomic`, `restrict` and
   object lifetime, which are not 6.5p6/p7 and are not what this module is for;
   and within sections 1-18, cases that differ from one already transcribed
   only in the scalar type involved are left to the corpus. *)

let ct_i16 : ctype = TScalar SInt16
let ct_i32 : ctype = TScalar SInt32
let ct_i64 : ctype = TScalar SInt64
let ct_f32 : ctype = TScalar SFloat32
let ct_f64 : ctype = TScalar SFloat64

(* struct point { int x; int y; } and struct nested { double d; struct point pt; } *)
let ct_point  : ctype = TStruct "point" 8 [(0, ct_i32); (4, ct_i32)]
let ct_nested : ctype = TStruct "nested" 16 [(0, ct_f64); (8, ct_point)]

(* Two distinct struct types with identical layout (case 13.3). *)
let ct_a : ctype = TStruct "a" 8 [(0, ct_i32); (4, ct_i32)]
let ct_b : ctype = TStruct "b" 8 [(0, ct_i32); (4, ct_i32)]

(* [DEFINED] 1.2: an `int` object read through `unsigned int *`. This is the
   case the counterpart rule exists for; before it was added the model
   rejected a program the standard explicitly permits. *)
let case_1_2_signed_unsigned_counterpart ()
  : Lemma (read_ok (etypes_of ct_i32 true) ct_u32 /\
           read_ok (etypes_of ct_u32 true) ct_i32)
  = ()

(* [DEFINED] 2.1: every byte of a declared `double` is readable as a character,
   at every offset. *)
let case_2_1_inspect_any_object_as_bytes (k: nat { k < 8 })
  : Lemma (read_ok (Seq.slice (etypes_of ct_f64 true) k (k + 1)) tchar)
  = ()

(* [DEFINED] 3.3: a store through `struct point *` into allocated storage gives
   it that effective type, and the members are then readable at `int`. *)
let case_3_3_struct_effective_type_then_member_access ()
  : Lemma (read_ok (Seq.slice (store_etypes (etypes_none 8) ct_point) 0 4) ct_i32 /\
           read_ok (Seq.slice (store_etypes (etypes_none 8) ct_point) 4 8) ct_i32)
  = ()

(* [DEFINED] 4.1: allocated storage is re-typed by each store in turn, and each
   read is paired with the store that installed its type. *)
let case_4_1_change_effective_type_repeatedly ()
  : Lemma (let e1 = store_etypes (etypes_none 4) ct_i32 in
           let e2 = store_etypes e1 ct_f32 in
           read_ok e1 ct_i32 /\ store_ok e1 ct_f32 /\ read_ok e2 ct_f32)
  = let e1 = store_etypes (etypes_none 4) ct_i32 in
    store_ok_read_ok (etypes_none 4) ct_i32;
    store_ok_read_ok e1 ct_f32

(* [DEFINED] 5.1 and 5.3: `memcpy` propagates the source's effective type into
   allocated storage -- and leaves it allocated, so 4.2 can still re-type it
   afterwards. *)
let case_5_1_memcpy_propagates_effective_type ()
  : Lemma (copy_etypes (etypes_none 8) (etypes_of ct_f64 true) == etypes_of ct_f64 false /\
           read_ok (copy_etypes (etypes_none 8) (etypes_of ct_f64 true)) ct_f64 /\
           store_ok (copy_etypes (etypes_none 8) (etypes_of ct_f64 true)) ct_i64)
  = Seq.lemma_eq_intro (copy_etypes (etypes_none 8) (etypes_of ct_f64 true))
                       (etypes_of ct_f64 false)

(* [DEFINED] 6.1: untouched allocated bytes have no effective type, so the
   first store may be at any type at all. *)
let case_6_1_fresh_malloc_write_is_always_legal (u: ctype)
  : Lemma (store_ok (etypes_none (csize u)) u)
  = ()

(* [UB] 13.1: an object declared `int`, read through `float *`. `float` is not
   compatible with `int`, is not its counterpart, and is not a character
   type. *)
let case_13_1_read_int_as_float ()
  : Lemma (~(read_ok (etypes_of ct_i32 true) ct_f32))
  = assert (eget (etypes_of ct_i32 true) 0 == Some ({ ty = ct_i32; off = 0; fixed = true }))

(* [UB] 13.2: an object declared `int`, *written* through `short *`. The store
   covers the first two bytes, and this is the case `store_ok` exists for: the
   relabelling function alone would make it a silent no-op. *)
let case_13_2_write_int_through_short ()
  : Lemma (~(store_ok (Seq.slice (etypes_of ct_i32 true) 0 2) ct_i16))
  = assert (eget (Seq.slice (etypes_of ct_i32 true) 0 2) 0
            == Some ({ ty = ct_i32; off = 0; fixed = true }))

(* [UB] 13.3: two struct types with identical layout are still different types.
   C compares tags, not shapes. *)
let case_13_3_struct_pun_between_layout_compatible_types ()
  : Lemma (~(read_ok (etypes_of ct_a true) ct_b))
  = assert (eget (etypes_of ct_a true) 0 == Some ({ ty = ct_a; off = 0; fixed = true }));
    assert (~(access_ok ct_a 0 ct_b))

(* [UB] 13.4 and 14.3: storage with a *declared* character-array type cannot be
   re-typed, which is what separates a `static char buf[]` arena from a
   `malloc`ed one. The character rule is about the type of the *lvalue*, not
   the type of the object, so it does not rescue this. *)
let case_13_4_char_array_used_as_int_storage ()
  : Lemma (~(store_ok (Seq.slice (etypes_of (TArr tchar 8) true) 0 4) ct_i32))
  = assert (eget (Seq.slice (etypes_of (TArr tchar 8) true) 0 4) 0
            == Some ({ ty = TArr tchar 8; off = 0; fixed = true }))

let case_14_3_reuse_of_a_declared_array_as_another_type ()
  : Lemma (~(store_ok (Seq.slice (etypes_of (TArr tchar 128) true) 0 8) ct_point))
  = assert (eget (Seq.slice (etypes_of (TArr tchar 128) true) 0 8) 0
            == Some ({ ty = TArr tchar 128; off = 0; fixed = true }))

(* [UB] 14.1: `memcpy` into a declared object does not re-type it. The copy
   itself is character-wise and so is permitted; what stays undefined is
   reading the result at the source's type. This is the case `copy_entry`'s
   `fixed` test exists for -- plain transport would relabel `dst`. *)
let case_14_1_memcpy_cannot_retype_a_declared_object ()
  : Lemma (copy_etypes (etypes_of ct_i32 true) (Seq.slice (etypes_of ct_f64 true) 0 4)
           == etypes_of ct_i32 true /\
           ~(read_ok (etypes_of ct_i32 true) ct_f32))
  = case_13_1_read_int_as_float ();
    Seq.lemma_eq_intro
      (copy_etypes (etypes_of ct_i32 true) (Seq.slice (etypes_of ct_f64 true) 0 4))
      (etypes_of ct_i32 true)

(* [UB] 14.2: storing a `float` into a declared `int` does not install `float`.
   A naive reading of 6.5p6's second rule says it does; `store_ok` is what says
   the store was undefined in the first place. *)
let case_14_2_store_does_not_retype_automatic_storage ()
  : Lemma (~(store_ok (etypes_of ct_i32 true) ct_f32))
  = assert (eget (etypes_of ct_i32 true) 0 == Some ({ ty = ct_i32; off = 0; fixed = true }))

(* [UB] 15.1: allocated storage typed `int` by a store, then read as `float`.
   The read is non-modifying, so it does not re-type anything. *)
let case_15_1_installed_int_read_as_float ()
  : Lemma (~(read_ok (store_etypes (etypes_none 4) ct_i32) ct_f32))
  = assert (eget (store_etypes (etypes_none 4) ct_i32) 0
            == Some ({ ty = ct_i32; off = 0; fixed = false }))

(* [UB] 15.2: allocated storage typed `struct point`, read as the larger and
   unrelated `struct nested`. *)
let case_15_2_installed_struct_read_as_unrelated_struct ()
  : Lemma (~(read_ok (Seq.append (store_etypes (etypes_none 8) ct_point) (etypes_none 8))
                     ct_nested))
  = assert (eget (Seq.append (store_etypes (etypes_none 8) ct_point) (etypes_none 8)) 0
            == Some ({ ty = ct_point; off = 0; fixed = false }))

(* [UB] 15.3: the effective type installed by `memcpy` binds just as the one
   installed by a store does. *)
let case_15_3_memcpy_installed_type_then_wrong_read ()
  : Lemma (~(read_ok (copy_etypes (etypes_none 8) (etypes_of ct_f64 true)) ct_i64))
  = assert (eget (copy_etypes (etypes_none 8) (etypes_of ct_f64 true)) 0
            == Some ({ ty = ct_f64; off = 0; fixed = false }))

(* [UB] 16.4: a partial store re-types only some of the bytes, and the larger
   object does not survive it. This is the case that justifies the index being
   per *byte* rather than per object. *)
let case_16_4_partial_overwrite_invalidates_the_whole ()
  : Lemma (let e0 = store_etypes (etypes_none 8) ct_f64 in
           let e1 = Seq.append (store_etypes (Seq.slice e0 0 4) ct_i32) (Seq.slice e0 4 8) in
           read_ok e0 ct_f64 /\ ~(read_ok e1 ct_f64))
  = let e0 = store_etypes (etypes_none 8) ct_f64 in
    let e1 = Seq.append (store_etypes (Seq.slice e0 0 4) ct_i32) (Seq.slice e0 4 8) in
    assert (eget e1 0 == Some ({ ty = ct_i32; off = 0; fixed = false }))

(* [UB] 18.1: R3's "if it has one" -- copying from a source that has no
   effective type installs none, so the destination is still untyped. That is
   *permissive* here rather than an error: an all-`None` index satisfies
   `read_ok` at every type, so the model accepts 18.1 where C calls it
   undefined. The value read is indeterminate, which is what actually makes
   18.1 undefined, and that is `uninit`'s job in `Pulse.Lib.C.Palow.Bytes` --
   no `_repr` relates a value to a range containing an uninitialized byte --
   not this module's. *)
let case_18_1_memcpy_from_an_untyped_source ()
  : Lemma (copy_etypes (etypes_none 8) (etypes_none 8) == etypes_none 8)
  = Seq.lemma_eq_intro (copy_etypes (etypes_none 8) (etypes_none 8)) (etypes_none 8)

(* [UB] 18.2, and a *known incompleteness*, recorded as a theorem so that it
   cannot be mistaken for enforcement.

   Copying the first half of one `double` over the first half of another leaves
   a chimera: C says no complete `double` object lives there any more. The
   model accepts it, and cannot do otherwise -- an entry records a type and an
   offset within an object, but no object *identity*, so bytes 0-3 of one
   `double` and bytes 4-7 of another are indistinguishable from the eight bytes
   of one.

   Detecting it would mean giving every object a ghost identity and threading
   it through every split and join, which is a large cost for a case no
   compiler's alias analysis exploits: the bytes agree with their claimed type,
   so no type-based optimisation is misled. The permissiveness is therefore
   deliberate, and is the reason this is a positive theorem. *)
let case_18_2_partial_memcpy_leaves_a_hybrid_is_accepted ()
  : Lemma (let e0 = store_etypes (etypes_none 8) ct_f64 in
           let src = Seq.slice (etypes_of ct_f64 true) 0 4 in
           let e1 = Seq.append (copy_etypes (Seq.slice e0 0 4) src) (Seq.slice e0 4 8) in
           read_ok e1 ct_f64)
  = ()

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
