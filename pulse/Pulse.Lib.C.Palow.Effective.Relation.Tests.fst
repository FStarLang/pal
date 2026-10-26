module Pulse.Lib.C.Palow.Effective.Relation.Tests

open Pulse.Lib.C.Palow.Effective.Relation

module ET = Pulse.Lib.C.Palow.Etype
module Seq = FStar.Seq

let u32 = ET.TScalar ET.SUInt32
let i32 = ET.TScalar ET.SInt32
let f32 = ET.TScalar ET.SFloat32
let a = ET.TStruct "A" 8 [(0, u32); (4, u32)]
let b = ET.TStruct "B" 8 [(0, u32); (4, u32)]
let fields = Seq.append (ET.etypes_of u32 false) (ET.etypes_of u32 false)

let nominal_tags_are_strict ()
  : Lemma (not (strict_subobject a 0 b) /\ not (strict_subobject b 0 a))
  = ()

let declared_nominal_cannot_be_reinterpreted ()
  : Lemma (not (view_read_ok (ET.etypes_of a true) b))
  = ()

let allocated_nominal_cannot_be_reinterpreted ()
  : Lemma (not (view_read_ok (ET.etypes_of a false) b))
  = ()

let fieldwise_initialized_view_is_not_nominal ()
  : Lemma (retains (ET.etypes_none 8) fields a /\
           view_read_ok fields a /\
           not (ET.read_ok fields a) /\
           not (ET.established_type fields a))
  = view_of_retains (ET.etypes_none 8) fields a;
    assert (ET.eget fields 0 ==
      Some ({ ET.ty = u32; ET.off = 0; ET.fixed = false }))

let independent_scalar_labels_are_not_a_nominal_parent ()
  : Lemma (not (ET.established_type fields a) /\
           not (ET.read_ok fields a) /\
           not (ET.copy_complete_ok
             (ET.prepare_write (ET.Ready (ET.etypes_none 8)) a)
             (ET.Ready fields)))
  = assert (ET.eget fields 0 ==
      Some ({ ET.ty = u32; ET.off = 0; ET.fixed = false }))

let ready_untyped_source_copy_is_currently_unsupported ()
  : Lemma (let src = ET.Ready (ET.etypes_none 4) in
           ET.source_type (ET.state_etypes src) == None /\
           not (ET.copy_complete_ok (ET.Ready (ET.etypes_none 4)) src) /\
           not (ET.copy_complete_ok (ET.Ready (ET.etypes_of u32 false)) src) /\
           ET.copy_entry None None == None)
  = ()

let prepared_target_cannot_use_untyped_source ()
  : Lemma (let src = ET.Ready (ET.etypes_none 4) in
           ET.state_read_ok src u32 /\
           not (ET.established_type (ET.state_etypes src) u32) /\
           not (ET.copy_complete_ok
             (ET.prepare_write (ET.Ready (ET.etypes_none 4)) u32) src))
  = ()

let all_mutable_is_insufficient_for_cross_type_ready_copy ()
  : Lemma (let dst = ET.etypes_of u32 false in
           ET.all_mutable dst /\ ET.elen dst == ET.csize f32 /\
           ET.full_mutable dst /\
           not (ET.copy_complete_ok (ET.Ready dst)
             (ET.Ready (ET.etypes_of f32 true))))
  = ()

let all_mutable_is_insufficient_for_mixed_ready_copy ()
  : Lemma (let dst = Seq.append (ET.etypes_none 4) (ET.etypes_of u32 false) in
           ET.all_mutable dst /\ ET.elen dst == ET.csize a /\
           not (ET.full_mutable dst) /\
           not (ET.copy_complete_ok (ET.Ready dst)
             (ET.Ready (ET.etypes_of a true))))
  = let dst = Seq.append (ET.etypes_none 4) (ET.etypes_of u32 false) in
    assert (ET.eget dst 0 == None);
    assert (ET.eget dst 4 ==
      Some ({ ET.ty = u32; ET.off = 0; ET.fixed = false }))

let scalar_cannot_import_a_foreign_parent ()
  : Lemma (not (retains (ET.etypes_none 4)
                (Seq.slice (ET.etypes_of a false) 0 4) u32))
  = assert (ET.eget (Seq.slice (ET.etypes_of a false) 0 4) 0 ==
      Some ({ ET.ty = a; ET.off = 0; ET.fixed = false }))

let character_access_is_not_a_subobject_path ()
  : Lemma (ET.access_ok u32 1 ET.tchar /\
           not (strict_subobject u32 1 ET.tchar) /\
           not (retains (ET.etypes_none 4)
             (Seq.init 4 (fun _ ->
               Some ({ ET.ty = ET.tchar; ET.off = 0; ET.fixed = false }))) u32))
  = ()

let character_read_of_owned_representation ()
  : Lemma (ET.read_ok (Seq.slice (ET.etypes_of a true) 3 4) ET.tchar)
  = ()

let signed_leaf_is_a_valid_subobject_view ()
  : Lemma (strict_subobject a 4 i32 /\
           retains (ET.etypes_none 4) (ET.etypes_of i32 false) u32 /\
           view_read_ok (ET.etypes_of i32 false) u32)
  = view_of_retains (ET.etypes_none 4) (ET.etypes_of i32 false) u32

let padding_cannot_receive_an_arbitrary_char_label ()
  : Lemma (let padded = ET.TStruct "Padded" 8 [(0, u32)] in
           ET.access_ok padded 6 ET.tchar /\
           not (strict_subobject padded 6 ET.tchar))
  = ()

let direct_disjoint_struct_field_is_safe ()
  : Lemma (view_slice_compatible a 4 u32 /\
           view_read_ok (Seq.slice fields 4 8) u32)
  = fieldwise_initialized_view_is_not_nominal ();
    view_read_ok_slice fields a 4 u32

let union_alternate_member_is_not_a_safe_view_slice ()
  : Lemma (let u = ET.TUnion "U" 4 [(0, u32); (0, f32)] in
           strict_subobject u 0 u32 /\
           view_read_ok (ET.etypes_of f32 false) u /\
           not (view_slice_compatible u 0 u32) /\
           not (view_read_ok (ET.etypes_of f32 false) u32))
  = let u = ET.TUnion "U" 4 [(0, u32); (0, f32)] in
    view_of_retains (ET.etypes_none 4) (ET.etypes_of f32 false) u;
    assert (ET.eget (ET.etypes_of f32 false) 0 ==
      Some ({ ET.ty = f32; ET.off = 0; ET.fixed = false }))

let enclosing_labels_project_only_with_context ()
  : Lemma (let current = ET.etypes_of a false in
           retains (ET.etypes_none 8) current a /\
           retains_at (ET.etypes_none 4) (Seq.slice current 4 8) a 4 /\
           not (retains (ET.etypes_none 4) (Seq.slice current 4 8) u32))
  = let current = ET.etypes_of a false in
    retains_slice (ET.etypes_none 8) current a 0 4 4;
    assert (ET.eget (Seq.slice current 4 8) 0 ==
      Some ({ ET.ty = a; ET.off = 4; ET.fixed = false }))

let child_relations_join_into_struct ()
  : Lemma (retains (ET.etypes_none 8) fields a)
  = retains_child_lift a 0 u32 (ET.etypes_none 4) (ET.etypes_of u32 false);
    retains_child_lift a 4 u32 (ET.etypes_none 4) (ET.etypes_of u32 false);
    retains_append (ET.etypes_none 4) (ET.etypes_of u32 false)
                   (ET.etypes_none 4) (ET.etypes_of u32 false) a 0;
    Seq.lemma_eq_intro (Seq.append (ET.etypes_none 4) (ET.etypes_none 4))
                      (ET.etypes_none 8)

let genuine_whole_store_establishes_nominal_type ()
  : Lemma (ET.read_ok (store_view_index fields a) a /\
           store_view_index fields a == ET.etypes_of a false /\
           ET.established_type (store_view_index fields a) a)
  = fieldwise_initialized_view_is_not_nominal ();
    store_view_read_ok fields a;
    store_view_allocated fields a

let declared_origin_survives_whole_store ()
  : Lemma (store_view_index (ET.etypes_of a true) a == ET.etypes_of a true)
  = Seq.lemma_eq_intro (store_view_index (ET.etypes_of a true) a)
                      (ET.etypes_of a true)

let whole_store_does_not_import_fixed_origin ()
  : Lemma (ET.all_mutable (store_view_index fields a))
  = store_view_allocated fields a

let zero_size_is_not_assumed_positive ()
  : Lemma (let empty = ET.TStruct "Empty" 0 [] in
           retains (ET.etypes_none 0) (ET.etypes_none 0) empty /\
           view_read_ok (ET.etypes_none 0) empty /\
           ET.read_ok (store_view_index (ET.etypes_none 0) empty) empty /\
           not (strict_subobject empty 0 empty))
  = let empty = ET.TStruct "Empty" 0 [] in
    view_of_retains (ET.etypes_none 0) (ET.etypes_none 0) empty;
    store_view_read_ok (ET.etypes_none 0) empty
