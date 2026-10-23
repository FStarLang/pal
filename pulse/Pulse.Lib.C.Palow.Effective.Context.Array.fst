module Pulse.Lib.C.Palow.Effective.Context.Array

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow

module A = Pulse.Lib.C.Palow.Array
module RA = Pulse.Lib.C.Palow.Effective.Retained.Array
module ET = Pulse.Lib.C.Palow.Etype
module Rel = Pulse.Lib.C.Palow.Effective.Relation
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas

let scalar_array_leaf_offset (width: pos) (i k off: nat)
  : Lemma
      (requires k < width /\ off < width /\
                0 <= width * i + k - off /\ (width * i + k - off) % width == 0)
      (ensures off == k)
  = let start = width * i + k - off in
    Math.modulo_distributivity start off width;
    Math.small_mod off width;
    Math.swap_mul width i;
    Math.multiple_modulo_lemma i width;
    Math.modulo_distributivity (width * i) k width;
    Math.small_mod k width

let scalar_array_slice_compatible (s: ET.scalar) (n: nat) (i: nat { i < n })
  : Lemma (Rel.view_slice_compatible (ET.TArr (ET.TScalar s) n)
             (ET.scalar_size s * i) (ET.TScalar s))
  = let ct = ET.TScalar s in
    let root = ET.TArr ct n in
    let width = ET.scalar_size s in
    A.elem_fits width n i;
    Math.swap_mul width i;
    Math.multiple_modulo_lemma i width;
    assert (Rel.strict_subobject root (width * i) ct);
    let aux (k: nat)
      : Lemma (forall (en: ET.etype_entry).
          k < ET.csize ct /\ en.ET.off < ET.csize en.ET.ty /\
          Rel.strict_subobject root (width * i + k - en.ET.off) en.ET.ty ==>
            ET.access_ok en.ET.ty (en.ET.off - k) ct \/
            Rel.strict_subobject ct (k - en.ET.off) en.ET.ty)
      = let inner (en: ET.etype_entry)
          : Lemma
              (k < ET.csize ct /\ en.ET.off < ET.csize en.ET.ty /\
               Rel.strict_subobject root (width * i + k - en.ET.off) en.ET.ty ==>
                 ET.access_ok en.ET.ty (en.ET.off - k) ct \/
                 Rel.strict_subobject ct (k - en.ET.off) en.ET.ty)
          = if k < ET.csize ct && en.ET.off < ET.csize en.ET.ty &&
               Rel.strict_subobject root (width * i + k - en.ET.off) en.ET.ty then
              if en.ET.ty = root then () else
              match en.ET.ty with
              | ET.TScalar leaf ->
                scalar_array_leaf_offset width i k en.ET.off;
                ET.counterpart_equivalence s leaf s;
                ET.counterpart_scalar_compatible leaf s
              | _ -> ()
        in Classical.forall_intro inner
    in Classical.forall_intro aux

(* Structural scalar-array views suffice for ordinary per-element reads.
   This never upgrades fieldwise scalar labels to a nominal TArr source. *)
let scalar_array_read_ok (s: ET.scalar) (n: nat) (e: ET.etypes)
  : Lemma
      (requires Rel.view_read_ok e (ET.TArr (ET.TScalar s) n))
      (ensures A.array_read_ok (ET.TScalar s) (ET.scalar_size s) n e)
  = let ct = ET.TScalar s in
    let width = ET.scalar_size s in
    Rel.view_base_retains e (ET.TArr ct n);
    let aux (i: nat)
      : Lemma (i < n ==> ET.read_ok (A.elem_etypes width e i) ct)
      = if i < n then begin
          A.elem_fits width n i;
          scalar_array_slice_compatible s n i;
          Rel.view_read_ok_slice e (ET.TArr ct n) (width * i) ct;
          Rel.view_scalar (A.elem_etypes width e i) s
        end
    in Classical.forall_intro aux

(* Array fields retain the real enclosing root, never a nominal array type
   inferred from scalar stores. A loan lets an ordinary elementwise array
   callee preserve its standalone baseline before restoring this context. *)
let value (#t: Type) (root: ET.ctype) (lo: nat) (ct: ET.ctype)
    (repr: t -> bytes -> prop) (esize alignment: nat) (base: ET.etypes)
    ([@@@mkey] a: ptr) (p: perm) (xs: Seq.seq t) : slprop =
  exists* actual. A.array_pts_to_at ct repr esize alignment a p xs actual
    ** pure (RA.scalar_element ct /\
             Rel.retains_at base actual root lo /\ Rel.view_region root lo base /\
             A.array_read_ok ct esize (Seq.length xs) base /\
             Rel.strict_subobject root lo (ET.TArr ct (Seq.length xs)))

let storage (#t: Type0) (root: ET.ctype) (lo: nat) (ct: ET.ctype)
    (repr: t -> bytes -> prop) (esize alignment n: nat)
    (base: ET.etypes) ([@@@mkey] a: ptr) : slprop =
  exists* xs. value root lo ct (A.maybe_repr repr esize) esize alignment base a 1.0R xs
    ** pure (Seq.length xs == n)

let loan (root: ET.ctype) (lo: nat) (ct: ET.ctype) (esize n: nat)
    ([@@@mkey] a: ptr) (base current: ET.etypes) : slprop =
  pure (RA.scalar_element ct /\
        Rel.retains_at base current root lo /\ Rel.view_region root lo base /\
        A.array_read_ok ct esize n base /\
        Rel.strict_subobject root lo (ET.TArr ct n))

let element_paths (root: ET.ctype) (lo: nat) (ct: ET.ctype) (esize n: nat)
  : Lemma
      (requires esize == ET.csize ct /\ 0 < esize /\
                Rel.strict_subobject root lo (ET.TArr ct n))
      (ensures forall (i: nat). i < n ==>
        Rel.strict_subobject root (lo + esize * i) ct)
  = let aux (i: nat) : Lemma (i < n ==>
        Rel.strict_subobject root (lo + esize * i) ct) =
      if i < n then begin
        A.elem_fits esize n i;
        Math.swap_mul esize i;
        Math.multiple_modulo_lemma i esize;
        Rel.strict_subobject_trans root lo (ET.TArr ct n) (esize * i) ct
      end
    in Classical.forall_intro aux

let slices_join (e: ET.etypes) (split: nat { split <= ET.elen e })
  : Lemma (Seq.append (Seq.slice e 0 split) (Seq.slice e split (ET.elen e)) == e)
  = Seq.lemma_eq_intro
      (Seq.append (Seq.slice e 0 split) (Seq.slice e split (ET.elen e))) e

(* Induction joins independently retained elements without assuming that their
   labels establish a nominal TArr. Bounds and paths are explicit premises,
   derived from the containing array field before invoking this helper. *)
let rec retains_elements_lift (root: ET.ctype) (lo: nat) (ct: ET.ctype)
    (esize n: nat) (base actual: ET.etypes)
  : Lemma
      (requires RA.retains ct esize n base actual /\
                lo + esize * n <= ET.csize root /\
                (forall (i: nat). i < n ==>
                  Rel.strict_subobject root (lo + esize * i) ct))
      (ensures Rel.retains_at base actual root lo)
      (decreases n)
  = if n = 0 then () else begin
      Math.lemma_mult_le_right esize 1 n;
      RA.retains_split ct esize n base actual 1;
      let b1 = Seq.slice base 0 esize in
      let a1 = Seq.slice actual 0 esize in
      let b2 = Seq.slice base esize (ET.elen base) in
      let a2 = Seq.slice actual esize (ET.elen actual) in
      Seq.lemma_eq_intro (Seq.slice b1 0 (ET.elen b1)) b1;
      Seq.lemma_eq_intro (Seq.slice a1 0 (ET.elen a1)) a1;
      Rel.retains_child_lift root lo ct b1 a1;
      let paths (i: nat) : Lemma (i < n - 1 ==>
        Rel.strict_subobject root (lo + esize + esize * i) ct) =
        if i < n - 1 then begin
          Math.distributivity_add_right esize 1 i;
          assert (lo + esize * (1 + i) == lo + esize + esize * i);
          assert (Rel.strict_subobject root (lo + esize * (1 + i)) ct)
        end
      in
      Classical.forall_intro paths;
      Math.distributivity_sub_right esize n 1;
      retains_elements_lift root (lo + esize) ct esize (n - 1) b2 a2;
      Rel.retains_append b1 a1 b2 a2 root lo;
      slices_join base esize;
      slices_join actual esize
    end

let retains_array_lift (root: ET.ctype) (lo: nat) (ct: ET.ctype)
    (esize n: nat) (base actual: ET.etypes)
  : Lemma
      (requires RA.retains ct esize n base actual /\ 0 < esize /\
                Rel.strict_subobject root lo (ET.TArr ct n))
      (ensures Rel.retains_at base actual root lo)
  = element_paths root lo ct esize n;
    retains_elements_lift root lo ct esize n base actual

ghost fn claim (#t: Type0) (root: ET.ctype) (lo: nat) (ct: ET.ctype)
    (repr: t -> bytes -> prop) (a: ptr) (esize alignment: SZ.t)
    (#p: perm) (#xs: Seq.seq t) (#base #actual: ET.etypes)
  requires A.array_pts_to_at ct repr (SZ.v esize) (SZ.v alignment) a p xs actual
  requires pure (RA.scalar_element ct /\
                 Rel.retains_at base actual root lo /\ Rel.view_region root lo base /\
                 A.array_read_ok ct (SZ.v esize) (Seq.length xs) base /\
                 Rel.strict_subobject root lo (ET.TArr ct (Seq.length xs)))
  ensures value root lo ct repr (SZ.v esize) (SZ.v alignment) base a p xs
{
  fold value root lo ct repr (SZ.v esize) (SZ.v alignment) base a p xs;
}

ghost fn reveal (#t: Type0) (root: ET.ctype) (lo: nat) (ct: ET.ctype)
    (repr: t -> bytes -> prop) (a: ptr) (esize alignment: SZ.t)
    (#p: perm) (#xs: Seq.seq t) (#base: ET.etypes)
  requires value root lo ct repr (SZ.v esize) (SZ.v alignment) base a p xs
  ensures exists* b actual. mem_pts_to_at a p b actual
    ** pure (RA.scalar_element ct /\
             A.array_repr repr (SZ.v esize) xs b /\
             A.array_aligned (SZ.v esize) (SZ.v alignment) a /\
             A.array_read_ok ct (SZ.v esize) (Seq.length xs) actual /\
             Rel.retains_at base actual root lo /\ Rel.view_region root lo base /\
             A.array_read_ok ct (SZ.v esize) (Seq.length xs) base /\
             Rel.strict_subobject root lo (ET.TArr ct (Seq.length xs)))
{
  unfold value root lo ct repr (SZ.v esize) (SZ.v alignment) base a p xs;
  A.array_reveal_at ct repr a esize alignment;
}

ghost fn borrow_array (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t)
    (#root: ET.ctype) (#lo: nat) (#p: perm) (#xs: Seq.seq t) (#base: ET.etypes)
  requires value root lo ct repr (SZ.v esize) (SZ.v alignment) base a p xs
  ensures exists* current.
    RA.value ct repr (SZ.v esize) (SZ.v alignment) current a p xs
    ** loan root lo ct (SZ.v esize) (Seq.length xs) a base current
{
  unfold value root lo ct repr (SZ.v esize) (SZ.v alignment) base a p xs;
  with actual. assert (A.array_pts_to_at ct repr (SZ.v esize) (SZ.v alignment) a p xs actual);
  A.array_reveal_at ct repr a esize alignment;
  with b. assert (mem_pts_to_at a p b actual);
  A.array_conceal_at ct repr a esize alignment #p #b #xs #actual;
  RA.retains_refl ct (SZ.v esize) (Seq.length xs) actual;
  RA.conceal ct repr a esize alignment #p #xs #actual #actual;
  fold loan root lo ct (SZ.v esize) (Seq.length xs) a base actual;
}

ghost fn restore_array (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment: SZ.t)
    (#root: ET.ctype) (#lo: nat) (#p: perm) (#xs: Seq.seq t) (#base #current: ET.etypes)
  requires loan root lo ct (SZ.v esize) (Seq.length xs) a base current
  requires RA.value ct repr (SZ.v esize) (SZ.v alignment) current a p xs
  ensures value root lo ct repr (SZ.v esize) (SZ.v alignment) base a p xs
{
  unfold loan root lo ct (SZ.v esize) (Seq.length xs) a base current;
  RA.reveal ct repr a esize alignment;
  with b actual. assert (mem_pts_to_at a p b actual);
  retains_array_lift root lo ct (SZ.v esize) (Seq.length xs) current actual;
  Rel.retains_at_trans base current actual root lo;
  A.array_conceal_at ct repr a esize alignment #p #b #xs #actual;
  claim root lo ct repr a esize alignment #p #xs #base #actual;
}

fn memset_zero (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment n nbytes: SZ.t) (z: t)
    (#root: ET.ctype) (#lo: nat)
    (#xs: erased (Seq.seq t)) (#base: ET.etypes)
  requires value root lo ct repr (SZ.v esize) (SZ.v alignment) base a 1.0R xs
  requires pure (Seq.length xs == SZ.v n /\ SZ.v nbytes == SZ.v esize * SZ.v n)
  requires pure (repr z (zeroed (SZ.v esize)))
  ensures value root lo ct repr (SZ.v esize) (SZ.v alignment) base a 1.0R
    (Seq.create (SZ.v n) z)
{
  borrow_array ct repr a esize alignment;
  with current. assert (RA.value ct repr (SZ.v esize) (SZ.v alignment)
    current a 1.0R xs);
  RA.memset_zero ct repr a esize alignment n nbytes z;
  restore_array ct repr a esize alignment
    #root #lo #1.0R #(Seq.create (SZ.v n) z) #base #current;
}

ghost fn borrow_storage (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment n: SZ.t)
    (#root: ET.ctype) (#lo: nat) (#base: ET.etypes)
  requires storage root lo ct repr (SZ.v esize) (SZ.v alignment) (SZ.v n) base a
  ensures exists* current.
    RA.storage ct repr (SZ.v esize) (SZ.v alignment) (SZ.v n) current a
    ** loan root lo ct (SZ.v esize) (SZ.v n) a base current
{
  unfold storage root lo ct repr (SZ.v esize) (SZ.v alignment) (SZ.v n) base a;
  with xs. assert (value root lo ct (A.maybe_repr repr (SZ.v esize))
    (SZ.v esize) (SZ.v alignment) base a 1.0R xs);
  borrow_array ct (A.maybe_repr repr (SZ.v esize)) a esize alignment;
  with current. assert (RA.value ct (A.maybe_repr repr (SZ.v esize))
    (SZ.v esize) (SZ.v alignment) current a 1.0R xs);
  fold RA.storage ct repr (SZ.v esize) (SZ.v alignment) (SZ.v n) current a;
}

ghost fn restore_storage (#t: Type0) (ct: ET.ctype) (repr: t -> bytes -> prop)
    (a: ptr) (esize alignment n: SZ.t)
    (#root: ET.ctype) (#lo: nat) (#base #current: ET.etypes)
  requires loan root lo ct (SZ.v esize) (SZ.v n) a base current
  requires RA.storage ct repr (SZ.v esize) (SZ.v alignment) (SZ.v n) current a
  ensures storage root lo ct repr (SZ.v esize) (SZ.v alignment) (SZ.v n) base a
{
  unfold RA.storage ct repr (SZ.v esize) (SZ.v alignment) (SZ.v n) current a;
  with xs. assert (RA.value ct (A.maybe_repr repr (SZ.v esize))
    (SZ.v esize) (SZ.v alignment) current a 1.0R xs);
  restore_array ct (A.maybe_repr repr (SZ.v esize)) a esize alignment;
  fold storage root lo ct repr (SZ.v esize) (SZ.v alignment) (SZ.v n) base a;
}

ghost fn forget (#t: Type0) (root: ET.ctype) (lo: nat) (ct: ET.ctype)
    (repr: t -> bytes -> prop) (a: ptr) (esize alignment: SZ.t)
    (#xs: Seq.seq t) (#base: ET.etypes)
  requires value root lo ct repr (SZ.v esize) (SZ.v alignment) base a 1.0R xs
  ensures storage root lo ct repr (SZ.v esize) (SZ.v alignment) (Seq.length xs) base a
{
  reveal root lo ct repr a esize alignment;
  with b actual. assert (mem_pts_to_at a 1.0R b actual);
  A.array_conceal_at ct (A.maybe_repr repr (SZ.v esize)) a esize alignment
    #1.0R #b #(A.somes xs) #actual;
  claim root lo ct (A.maybe_repr repr (SZ.v esize)) a esize alignment
    #1.0R #(A.somes xs) #base #actual;
  fold storage root lo ct repr (SZ.v esize) (SZ.v alignment) (Seq.length xs) base a;
}

let model_allocated_parent_labels_survive_array_calls ()
  : Lemma
      (let ct = ET.TScalar ET.SUInt32 in
       let parent = ET.TStruct "Parent" 8 [(0, ET.TArr ct 2)] in
       let base = ET.etypes_of parent false in
       A.array_read_ok ct 4 2 base /\
       RA.retains ct 4 2 base base /\
       Rel.view_region parent 0 base /\
       Rel.retains_at base base parent 0 /\
       Rel.strict_subobject parent 0 (ET.TArr ct 2))
  = ()

let model_same_layout_parent_cannot_gain_context ()
  : Lemma
      (let ct = ET.TScalar ET.SUInt32 in
       let parent = ET.TStruct "Parent" 8 [(0, ET.TArr ct 2)] in
       let foreign = ET.TStruct "Foreign" 8 [(0, ET.TArr ct 2)] in
       not (Rel.view_region parent 0 (ET.etypes_of foreign false)))
  = ()
