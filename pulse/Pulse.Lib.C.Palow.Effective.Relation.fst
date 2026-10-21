module Pulse.Lib.C.Palow.Effective.Relation

module ET = Pulse.Lib.C.Palow.Etype
module Seq = FStar.Seq

open Pulse.Lib.C.Palow.Etype

(* A typed subobject path, not a byte-access exemption. In particular a char
   label can be introduced only at an actual char subobject. Scalar leaves
   admit C's corresponding signed/unsigned access views, but aggregate tags
   remain nominal. Every step, including the root, checks its extent. *)
(* Unlike `ET.type_compatible`, this relation is transitive: an enumerated
   type is a subobject path only to itself, never to its underlying integer
   type. That access remains allowed by `ET.access_ok`, but it does not make a
   path through which a different enumerated type could be reached. *)
let strict_compatible (ct: ET.ctype) (child: ET.ctype) : bool =
  ET.nominal_compatible ct child ||
  (match ct, child with
   | ET.TScalar s, ET.TScalar v -> ET.counterpart_compatible s v
   | _ -> false)

let strict_compatible_type_compatible (ct: ET.ctype) (child: ET.ctype)
  : Lemma (requires strict_compatible ct child)
          (ensures ET.type_compatible ct child)
  = match ct, child with
    | ET.TScalar s, ET.TScalar v -> ET.counterpart_scalar_compatible s v
    | _ -> ()

let rec strict_subobject (ct: ET.ctype) (off: int) (child: ET.ctype)
  : Tot bool (decreases %[ET.ctype_size ct; 0]) =
  0 < ET.csize child && 0 <= off && off + ET.csize child <= ET.csize ct &&
  ((off = 0 && strict_compatible ct child) ||
   (match ct with
    | ET.TScalar _ -> false
    | ET.TArr element n ->
      off < ET.csize element * n &&
      strict_subobject element (ET.emod off (ET.csize element)) child
    | ET.TStruct _ _ members | ET.TUnion _ _ members ->
      strict_subobject_members members off child))
and strict_subobject_members (members: list (nat & ET.ctype))
    (off: int) (child: ET.ctype)
  : Tot bool (decreases %[ET.members_size members; 1]) =
  match members with
  | [] -> false
  | (offset, ct) :: rest ->
    strict_subobject ct (off - offset) child ||
    strict_subobject_members rest off child

let strict_subobject_refl (ct: ET.ctype { 0 < ET.csize ct })
  : Lemma (strict_subobject ct 0 ct) = ()

(* A subobject path never changes enumerated type at a scalar, so it may be
   composed with any further access. *)
let strict_subobject_compose_ok (ct: ET.ctype) (off: int) (child: ET.ctype)
  : Lemma (requires strict_subobject ct off child)
          (ensures ET.compose_ok ct child)
  = ()

let rec strict_subobject_access (ct: ET.ctype) (off: int) (child: ET.ctype)
  : Lemma (requires strict_subobject ct off child)
          (ensures ET.access_ok ct off child)
          (decreases %[ET.ctype_size ct; 0])
  = if off = 0 && strict_compatible ct child then
      strict_compatible_type_compatible ct child
    else match ct with
    | ET.TScalar _ -> ()
    | ET.TArr element _ ->
      strict_subobject_access element (ET.emod off (ET.csize element)) child
    | ET.TStruct _ _ members | ET.TUnion _ _ members ->
      strict_subobject_members_access members off child
and strict_subobject_members_access (members: list (nat & ET.ctype))
    (off: int) (child: ET.ctype)
  : Lemma (requires strict_subobject_members members off child)
          (ensures ET.access_ok_members members off child)
          (decreases %[ET.members_size members; 1])
  = match members with
    | [] -> ()
    | (offset, ct) :: rest ->
      if strict_subobject ct (off - offset) child then
        strict_subobject_access ct (off - offset) child
      else strict_subobject_members_access rest off child

let rec strict_subobject_trans (ct: ET.ctype) (off: int) (child: ET.ctype)
    (inner: int) (leaf: ET.ctype)
  : Lemma (requires strict_subobject ct off child /\
                    strict_subobject child inner leaf)
          (ensures strict_subobject ct (off + inner) leaf)
          (decreases %[ET.ctype_size ct; 0])
  = if off = 0 && strict_compatible ct child then
      (match ct, child, leaf with
       | ET.TScalar a, ET.TScalar b, ET.TScalar c ->
         ET.counterpart_equivalence a b c
       | _ -> ())
    else match ct with
    | ET.TScalar _ -> ()
    | ET.TArr element _ ->
      strict_subobject_trans element (ET.emod off (ET.csize element)) child inner leaf;
      if ET.csize element > 0 then
        ET.mod_add_no_carry off (ET.csize element) inner
    | ET.TStruct _ _ members | ET.TUnion _ _ members ->
      strict_subobject_members_trans members off child inner leaf
and strict_subobject_members_trans (members: list (nat & ET.ctype))
    (off: int) (child: ET.ctype) (inner: int) (leaf: ET.ctype)
  : Lemma (requires strict_subobject_members members off child /\
                    strict_subobject child inner leaf)
          (ensures strict_subobject_members members (off + inner) leaf)
          (decreases %[ET.members_size members; 1])
  = match members with
    | [] -> ()
    | (offset, ct) :: rest ->
      if strict_subobject ct (off - offset) child then
        strict_subobject_trans ct (off - offset) child inner leaf
      else strict_subobject_members_trans rest off child inner leaf

(* A slice retains its original root context. This matters when a previously
   untyped parent acquires a whole-parent label: its child slice still contains
   that enclosing label, not a newly manufactured standalone child object.
   Projecting to a different root without this context is not sound. *)
let retains_entry (root: ET.ctype) (position: nat)
    (base actual: option ET.etype_entry) : prop =
    (match base with
     | Some en -> actual == Some en
     | None ->
       match actual with
       | None -> True
       | Some en ->
         not en.fixed /\ en.off < ET.csize en.ty /\
         strict_subobject root (position - en.off) en.ty)

let retains_at (base actual: ET.etypes) (root: ET.ctype) (lo: nat) : prop =
  ET.elen base == ET.elen actual /\ lo + ET.elen base <= ET.csize root /\
  (forall (k: nat). k < ET.elen base ==>
    retains_entry root (lo + k) (ET.eget base k) (ET.eget actual k))

let retains (base actual: ET.etypes) (ct: ET.ctype) : prop =
  ET.elen base == ET.csize ct /\ retains_at base actual ct 0

let retains_at_refl (e: ET.etypes) (root: ET.ctype)
    (lo: nat { lo + ET.elen e <= ET.csize root })
  : Lemma (retains_at e e root lo) = ()

let retains_refl (e: ET.etypes) (ct: ET.ctype { ET.elen e == ET.csize ct })
  : Lemma (retains e e ct) = ()

let retains_at_trans (base middle actual: ET.etypes) (root: ET.ctype) (lo: nat)
  : Lemma (requires retains_at base middle root lo /\ retains_at middle actual root lo)
          (ensures retains_at base actual root lo) = ()

let retains_trans (base middle actual: ET.etypes) (ct: ET.ctype)
  : Lemma (requires retains base middle ct /\ retains middle actual ct)
          (ensures retains base actual ct) = ()

let retains_slice (base actual: ET.etypes) (root: ET.ctype) (lo: nat)
    (off: nat) (n: nat { off + n <= ET.elen base /\ off + n <= ET.elen actual })
  : Lemma (requires retains_at base actual root lo)
          (ensures retains_at (Seq.slice base off (off + n))
                              (Seq.slice actual off (off + n)) root (lo + off))
  = let aux (k: nat { k < n })
      : Lemma (retains_entry root (lo + off + k)
                 (ET.eget (Seq.slice base off (off + n)) k)
                 (ET.eget (Seq.slice actual off (off + n)) k))
      = assert (retains_entry root (lo + (off + k))
                  (ET.eget base (off + k)) (ET.eget actual (off + k)))
    in FStar.Classical.forall_intro aux

(* A standalone child relation can be lifted into a strict parent path.
   In contrast, projecting an enclosing-label relation into a standalone
   child relation is generally false; use retains_slice for that direction. *)
let retains_lift (base actual: ET.etypes) (parent: ET.ctype)
    (off: nat) (child: ET.ctype)
  : Lemma (requires retains base actual child /\ strict_subobject parent off child)
          (ensures retains_at base actual parent off)
  = let aux (k: nat { k < ET.elen base })
      : Lemma
          (match ET.eget base k, ET.eget actual k with
           | None, Some en -> strict_subobject parent (off + k - en.off) en.ty
           | _ -> True)
      = match ET.eget base k, ET.eget actual k with
        | None, Some en -> strict_subobject_trans parent off child (k - en.off) en.ty
        | _ -> ()
    in FStar.Classical.forall_intro aux

let retains_child_lift (parent: ET.ctype) (off: nat) (child: ET.ctype)
    (base actual: ET.etypes)
  : Lemma (requires retains base actual child /\ strict_subobject parent off child)
          (ensures retains_at base actual parent off)
  = retains_lift base actual parent off child

let retains_append (b1 a1 b2 a2: ET.etypes) (root: ET.ctype) (lo: nat)
  : Lemma (requires retains_at b1 a1 root lo /\
                    retains_at b2 a2 root (lo + ET.elen b1))
          (ensures retains_at (Seq.append b1 b2) (Seq.append a1 a2) root lo)
  = ()

let retains_join_slices (base actual1 actual2: ET.etypes) (root: ET.ctype)
    (lo: nat) (split: nat { split <= ET.elen base })
  : Lemma
      (requires retains_at (Seq.slice base 0 split) actual1 root lo /\
                retains_at (Seq.slice base split (ET.elen base)) actual2 root (lo + split))
      (ensures retains_at base (Seq.append actual1 actual2) root lo)
  = retains_append (Seq.slice base 0 split) actual1
                   (Seq.slice base split (ET.elen base)) actual2 root lo;
    Seq.lemma_eq_intro
      (Seq.append (Seq.slice base 0 split) (Seq.slice base split (ET.elen base))) base

let retains_join_prefix (base actual1 actual2: ET.etypes) (root: ET.ctype)
    (lo: nat) (split: nat) (upper: nat { split <= upper /\ upper <= ET.elen base })
  : Lemma
      (requires retains_at (Seq.slice base 0 split) actual1 root lo /\
                retains_at (Seq.slice base split upper) actual2 root (lo + split))
      (ensures retains_at (Seq.slice base 0 upper) (Seq.append actual1 actual2) root lo)
  = retains_append (Seq.slice base 0 split) actual1
                   (Seq.slice base split upper) actual2 root lo;
    Seq.lemma_eq_intro
      (Seq.append (Seq.slice base 0 split) (Seq.slice base split upper))
      (Seq.slice base 0 upper)

let retains_finish (base actual: ET.etypes) (ct: ET.ctype)
  : Lemma (requires retains_at base actual ct 0 /\ ET.elen base == ET.csize ct)
          (ensures retains base actual ct) = ()

let retains_store (e: ET.etypes) (ct: ET.ctype { ET.elen e == ET.csize ct })
  : Lemma (requires ET.read_ok e ct)
          (ensures retains e (ET.store_etypes e ct) ct) = ()

(* Structural view evidence is weaker than nominal effective type evidence.
   It can justify a genuine typed store after fieldwise initialization, but
   cannot be used as an established_type source certificate for memcpy. *)
let view_read_ok (actual: ET.etypes) (ct: ET.ctype) : prop =
  exists (baseline: ET.etypes). ET.read_ok baseline ct /\ retains baseline actual ct

let view_of_retains (base actual: ET.etypes) (ct: ET.ctype)
  : Lemma (requires ET.read_ok base ct /\ retains base actual ct)
          (ensures view_read_ok actual ct) = ()

let read_ok_view (actual: ET.etypes) (ct: ET.ctype)
  : Lemma (requires ET.read_ok actual ct)
          (ensures view_read_ok actual ct)
  = retains_refl actual ct

let view_retains (base actual: ET.etypes) (ct: ET.ctype)
  : Lemma (requires view_read_ok base ct /\ retains base actual ct)
          (ensures view_read_ok actual ct)
  = let aux (baseline: ET.etypes)
      : Lemma (requires ET.read_ok baseline ct /\ retains baseline base ct)
              (ensures ET.read_ok baseline ct /\ retains baseline actual ct)
      = retains_trans baseline base actual ct
    in assert (forall baseline.
      ET.read_ok baseline ct /\ retains baseline base ct ==>
      ET.read_ok baseline ct /\ retains baseline actual ct)

(* Canonically remember exactly the entries that already license the whole
   access. Entries representing only contained subobjects are left untyped in
   the baseline, not promoted to nominal enclosing-object evidence. *)
let view_base (e: ET.etypes) (ct: ET.ctype) : ET.etypes =
  Seq.init (ET.elen e) (fun k ->
    match ET.eget e k with
    | None -> None
    | Some en ->
      if ET.access_ok en.ty (en.off - k) ct then Some en else None)

let view_base_read_ok (e: ET.etypes) (ct: ET.ctype { ET.elen e == ET.csize ct })
  : Lemma (ET.read_ok (view_base e ct) ct) = ()

let view_base_retains (e: ET.etypes) (ct: ET.ctype)
  : Lemma (requires view_read_ok e ct)
          (ensures ET.read_ok (view_base e ct) ct /\ retains (view_base e ct) e ct)
  = ()

let view_read_ok_entry (e: ET.etypes) (ct: ET.ctype)
    (k: nat { k < ET.elen e })
  : Lemma
      (requires view_read_ok e ct)
      (ensures
        (match ET.eget e k with
        | None -> True
        | Some en ->
          ET.access_ok en.ty (en.off - k) ct \/
          (not en.fixed /\ en.off < ET.csize en.ty /\
           strict_subobject ct (k - en.off) en.ty)))
  = view_base_retains e ct

let view_scalar (e: ET.etypes) (scalar: ET.scalar)
  : Lemma (view_read_ok e (ET.TScalar scalar) <==>
           ET.read_ok e (ET.TScalar scalar))
  = let aux (en: ET.etype_entry) (k: nat)
      : Lemma
          (requires en.off < ET.csize en.ty /\
                    strict_subobject (ET.TScalar scalar) (k - en.off) en.ty)
          (ensures ET.access_ok en.ty (en.off - k) (ET.TScalar scalar))
      = match en.ty with
        | ET.TScalar s ->
          ET.counterpart_equivalence scalar s scalar;
          ET.counterpart_scalar_compatible s scalar
        | _ -> ()
    in ()

(* Per-region structural evidence needs no remembered whole-object baseline.
   The position is relative to the root, not relative to this byte's slice.
   These guards compose views, never nominal effective-type certificates. *)
let view_entry (root: ET.ctype) (position: nat)
    (entry: option ET.etype_entry) : prop =
  match entry with
  | None -> True
  | Some en ->
    ET.access_ok en.ty (en.off - position) root \/
    (not en.fixed /\ en.off < ET.csize en.ty /\
     strict_subobject root (position - en.off) en.ty)

let view_region (root: ET.ctype) (lo: nat) (e: ET.etypes) : prop =
  lo + ET.elen e <= ET.csize root /\
  (forall (k: nat). k < ET.elen e ==> view_entry root (lo + k) (ET.eget e k))

let view_region_of_view (e: ET.etypes) (root: ET.ctype)
  : Lemma (requires view_read_ok e root)
          (ensures view_region root 0 e)
  = view_base_retains e root

let view_region_slice (e: ET.etypes) (root: ET.ctype) (lo: nat)
    (off: nat) (n: nat { off + n <= ET.elen e })
  : Lemma (requires view_region root lo e)
          (ensures view_region root (lo + off) (Seq.slice e off (off + n)))
  = let aux (k: nat { k < n })
      : Lemma (view_entry root (lo + off + k)
                 (ET.eget (Seq.slice e off (off + n)) k))
      = assert (view_entry root (lo + (off + k)) (ET.eget e (off + k)))
    in FStar.Classical.forall_intro aux

let view_region_preserved (base actual: ET.etypes) (root: ET.ctype)
    (lo: nat) (child: ET.ctype)
  : Lemma (requires view_region root lo base /\ retains base actual child /\
                    strict_subobject root lo child)
          (ensures view_region root lo actual)
  = let aux (k: nat { k < ET.elen actual })
      : Lemma (view_entry root (lo + k) (ET.eget actual k))
      = match ET.eget base k, ET.eget actual k with
        | None, Some en ->
          strict_subobject_trans root lo child (k - en.off) en.ty
        | _ -> ()
    in FStar.Classical.forall_intro aux

let view_region_append (root: ET.ctype) (lo: nat) (e1 e2: ET.etypes)
  : Lemma (requires view_region root lo e1 /\
                    view_region root (lo + ET.elen e1) e2)
          (ensures view_region root lo (Seq.append e1 e2))
  = ()

let view_region_finish (e: ET.etypes) (root: ET.ctype)
  : Lemma (requires view_region root 0 e /\ ET.elen e == ET.csize root)
          (ensures view_read_ok e root)
  = view_base_read_ok e root;
    assert (retains (view_base e root) e root)

(* This sufficient non-overlap condition is explicit: a union's arbitrary
   alternate-member view does NOT automatically satisfy it. It can be checked
   for generated, concrete struct layouts without assuming a nominal type
   from field labels. The first alternative covers genuine enclosing labels;
   the second covers typed subobjects contained in the selected child. *)
let view_slice_compatible (parent: ET.ctype) (off: nat) (child: ET.ctype) : prop =
  strict_subobject parent off child /\
  (forall (k: nat) (en: ET.etype_entry).
    k < ET.csize child /\ en.off < ET.csize en.ty /\
    strict_subobject parent (off + k - en.off) en.ty ==>
      ET.access_ok en.ty (en.off - k) child \/
      strict_subobject child (k - en.off) en.ty)

let view_read_ok_slice (e: ET.etypes) (parent: ET.ctype) (off: nat)
    (child: ET.ctype { off + ET.csize child <= ET.elen e })
  : Lemma (requires view_read_ok e parent /\ view_slice_compatible parent off child)
          (ensures view_read_ok (Seq.slice e off (off + ET.csize child)) child)
  = let part = Seq.slice e off (off + ET.csize child) in
    strict_subobject_access parent off child;
    view_base_read_ok part child;
    let aux (k: nat { k < ET.csize child })
      : Lemma (retains_entry child k
                 (ET.eget (view_base part child) k) (ET.eget part k))
      = match ET.eget part k with
        | None -> ()
        | Some en ->
          if ET.access_ok en.ty (en.off - k) child then () else begin
            assert (ET.eget e (off + k) == Some en);
            view_read_ok_entry e parent (off + k);
            if ET.access_ok en.ty (en.off - (off + k)) parent then begin
              strict_subobject_compose_ok parent off child;
              ET.access_ok_trans en.ty (en.off - (off + k)) parent off child
            end;
            assert (not en.fixed /\ en.off < ET.csize en.ty /\
                    strict_subobject parent (off + k - en.off) en.ty);
            assert (strict_subobject child (k - en.off) en.ty)
          end
    in
    FStar.Classical.forall_intro aux;
    assert (retains (view_base part child) part child)

(* This computes the successor index ONLY for a genuine whole typed store,
   not a ghost permission to relabel bytes. Declared and already-compatible
   enclosing labels remain immutable. Allocated field labels that do not
   license the whole storing lvalue are replaced by that actual lvalue type.
   Character stores do not independently establish a noncharacter object. *)
let store_view_index (e: ET.etypes) (ct: ET.ctype { ET.elen e == ET.csize ct })
  : result:ET.etypes { ET.elen result == ET.elen e } =
  if ET.character_type ct then e else ET.store_etypes e ct

let store_view_read_ok (e: ET.etypes) (ct: ET.ctype { ET.elen e == ET.csize ct })
  : Lemma (requires view_read_ok e ct)
          (ensures ET.read_ok (store_view_index e ct) ct)
  = ()

let store_view_fixed_origin (e: ET.etypes) (ct: ET.ctype { ET.elen e == ET.csize ct })
    (k: nat { k < ET.elen e })
  : Lemma
      (match ET.eget (store_view_index e ct) k with
       | None -> ET.eget e k == None
       | Some after ->
         if after.fixed then ET.eget e k == Some after
         else match ET.eget e k with
              | None -> True
              | Some before -> not before.fixed)
  = ()

let store_view_allocated (e: ET.etypes) (ct: ET.ctype { ET.elen e == ET.csize ct })
  : Lemma (requires ET.all_mutable e /\ not (ET.character_type ct) /\
                    (forall (k: nat). k < ET.elen e ==>
                      (match ET.eget e k with
                       | None -> True
                       | Some en -> not (ET.access_ok en.ty (en.off - k) ct))))
          (ensures store_view_index e ct == ET.etypes_of ct false)
  = Seq.lemma_eq_intro (store_view_index e ct) (ET.etypes_of ct false)
