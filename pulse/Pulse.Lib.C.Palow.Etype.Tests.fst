module Pulse.Lib.C.Palow.Etype.Tests

open Pulse.Lib.C.Palow.Etype

module Seq = FStar.Seq

let ct_i32 = TScalar SInt32
let ct_f32 = TScalar SFloat32

let signed_unsigned_access ()
  : Lemma (access_ok (TScalar SInt16) 0 (TScalar SUInt16) /\
           access_ok (TScalar SUInt16) 0 (TScalar SInt16) /\
           access_ok ct_i32 0 ct_u32 /\ access_ok ct_u32 0 ct_i32 /\
           access_ok (TScalar SInt64) 0 (TScalar SUInt64) /\
           access_ok (TScalar SUInt64) 0 (TScalar SInt64))
  = ()

let signed_unsigned_composes ()
  : Lemma (access_ok ct_S 0 ct_i32 /\ access_ok ct_i32 0 ct_u32 /\
           access_ok ct_S 0 ct_u32)
  = access_ok_trans ct_S 0 ct_i32 0 ct_u32

let signed_char_is_character ()
  : Lemma (access_ok ct_f32 1 (TScalar SInt8) /\
           access_ok ct_i32 1 tchar)
  = ()

let layout_is_not_type_compatibility ()
  : Lemma (layout_compatible ct_i32 ct_f32 /\
           ~(nominal_compatible ct_i32 ct_u32) /\
           type_compatible ct_i32 ct_u32 /\
           ~(type_compatible ct_i32 ct_f32) /\
           ~(access_ok ct_i32 0 ct_f32) /\
           ~(access_ok ct_u32 0 ct_ptr))
  = ()

let equal_layout_different_tags ()
  : Lemma (let other = TStruct "Other" 8 [(0, ct_u32); (4, ct_u32)] in
           layout_compatible ct_T other /\
           ~(nominal_compatible ct_T other) /\
           ~(access_ok ct_T 0 other))
  = ()

let fresh_fallback_is_not_establishment ()
  : Lemma (let s = Ready (etypes_none 4) in
           state_read_ok s ct_i32 /\ state_read_ok s ct_f32 /\
           ~(established_type (state_etypes s) ct_i32) /\
           source_type (state_etypes s) == None)
  = ()

let preparation_is_not_a_read ()
  : Lemma (let old = etypes_of ct_i32 false in
           let p = prepare_write (Ready old) ct_f32 in
           state_etypes p == old /\
           ~(state_read_ok p ct_f32) /\ ~(state_read_ok p ct_i32) /\
           ~(state_read_ok p tchar))
  = ()

let preparation_is_not_a_source ()
  : Lemma (let p = prepare_write (Ready (etypes_none 4)) ct_i32 in
           ~(copy_complete_ok (Ready (etypes_none 4)) p) /\
           ~(copy_complete_ok (Ready (etypes_of ct_f32 true)) p))
  = ()

let declared_preparation_denied ()
  : Lemma (~(prepare_write_ok (Ready (etypes_of ct_i32 true)) ct_f32))
  = assert (eget (etypes_of ct_i32 true) 0 ==
            Some ({ ty = ct_i32; off = 0; fixed = true }))

let partial_preparation_denied ()
  : Lemma (~(prepare_write_ok
             (Ready (Seq.slice (etypes_of ct_T false) 0 4)) ct_i32))
  = assert (eget (Seq.slice (etypes_of ct_T false) 0 4) 0 ==
            Some ({ ty = ct_T; off = 0; fixed = false }))

let pending_store_completes_at_actual_type ()
  : Lemma (let p = prepare_write (Ready (etypes_of ct_i32 false)) ct_f32 in
           store_complete_ok p ct_f32 /\
           ~(store_complete_ok p ct_i32) /\
           state_etypes (complete_store p ct_f32) == etypes_of ct_f32 false /\
           state_read_ok (complete_store p ct_f32) ct_f32)
  = let p = prepare_write (Ready (etypes_of ct_i32 false)) ct_f32 in
    Seq.lemma_eq_intro (state_etypes (complete_store p ct_f32))
                      (etypes_of ct_f32 false)

let scalar_member_does_not_install_union ()
  : Lemma (let u = TUnion "One" 4 [(0, ct_i32)] in
           let p = prepare_write (Ready (etypes_none 4)) u in
           ~(store_complete_ok p ct_i32) /\
           ~(store_complete_ok p tchar) /\
           store_complete_ok p u)
  = ()

let character_store_does_not_establish ()
  : Lemma (let s = Ready (etypes_none 1) in
           state_etypes (complete_store s tchar) == etypes_none 1 /\
           ~(established_type (state_etypes (complete_store s tchar)) (TScalar SBool)))
  = ()

let character_cannot_complete_noncharacter ()
  : Lemma (let p = prepare_write (Ready (etypes_none 1)) (TScalar SBool) in
           ~(store_complete_ok p tchar) /\
           ~(store_complete_ok p (TScalar SInt8)))
  = ()

let typed_cross_type_declared_store_denied ()
  : Lemma (~(store_complete_ok (Ready (etypes_of ct_i32 true)) ct_f32))
  = assert (eget (etypes_of ct_i32 true) 0 ==
            Some ({ ty = ct_i32; off = 0; fixed = true }))

(* Byte copying differs from a typed store: the destination's declared type
   remains authoritative even when the source holds another type. *)
let fixed_cross_type_copy_allowed ()
  : Lemma (let dst = Ready (etypes_of ct_f32 true) in
           let src = Ready (etypes_of ct_i32 true) in
           copy_complete_ok dst src /\
           state_etypes (complete_copy dst src) == etypes_of ct_f32 true)
  = complete_copy_declared_stable (Ready (etypes_of ct_f32 true))
                                 (Ready (etypes_of ct_i32 true))

let allocated_mismatched_copy_denied ()
  : Lemma (~(copy_complete_ok (Ready (etypes_of ct_f32 false))
                             (Ready (etypes_of ct_i32 true))))
  = assert (eget (etypes_of ct_f32 false) 0 ==
            Some ({ ty = ct_f32; off = 0; fixed = false }))

let prepared_copy_checks_established_source ()
  : Lemma (let dst = prepare_write (Ready (etypes_of ct_f32 false)) ct_i32 in
           copy_complete_ok dst (Ready (etypes_of ct_i32 true)) /\
           ~(copy_complete_ok dst (Ready (etypes_of ct_f32 true))) /\
           ~(copy_complete_ok dst (Ready (etypes_none 4))))
  = assert (eget (etypes_of ct_f32 true) 0 ==
            Some ({ ty = ct_f32; off = 0; fixed = true }))

let copy_never_launders_fixed_origin ()
  : Lemma (let dst = prepare_write (Ready (etypes_of ct_f32 false)) ct_i32 in
           let copied = complete_copy dst (Ready (etypes_of ct_i32 true)) in
           state_etypes copied == etypes_of ct_i32 false /\
           prepare_write_ok copied ct_f32 /\
           state_read_ok copied ct_i32)
  = let dst = prepare_write (Ready (etypes_of ct_f32 false)) ct_i32 in
    Seq.lemma_eq_intro
      (state_etypes (complete_copy dst (Ready (etypes_of ct_i32 true))))
      (etypes_of ct_i32 false)

let fresh_initial_copy_allowed ()
  : Lemma (let dst = Ready (etypes_none 4) in
           let src = Ready (etypes_of ct_i32 false) in
           copy_complete_ok dst src /\
           state_etypes (complete_copy dst src) == etypes_of ct_i32 false)
  = Seq.lemma_eq_intro
      (state_etypes (complete_copy (Ready (etypes_none 4))
                                   (Ready (etypes_of ct_i32 false))))
      (etypes_of ct_i32 false)

let partial_source_is_not_whole_object ()
  : Lemma (let src = Ready (Seq.slice (etypes_of ct_T true) 0 4) in
           state_read_ok src ct_u32 /\
           ~(copy_complete_ok (Ready (etypes_none 4)) src) /\
           ~(copy_complete_ok
             (prepare_write (Ready (etypes_none 4)) ct_u32) src))
  = assert (eget (Seq.slice (etypes_of ct_T true) 0 4) 0 ==
            Some ({ ty = ct_T; off = 0; fixed = true }))

let fields_are_not_an_established_source ()
  : Lemma (let src = Ready (Seq.append (etypes_of ct_u32 false)
                                       (etypes_of ct_u32 false)) in
           ~(copy_complete_ok
             (prepare_write (Ready (etypes_none 8)) ct_T) src))
  = assert (eget (Seq.append (etypes_of ct_u32 false) (etypes_of ct_u32 false)) 0 ==
            Some ({ ty = ct_u32; off = 0; fixed = false }))

let partial_declared_copy_preserves_whole_index ()
  : Lemma (let whole = etypes_of ct_T true in
           let dst = Ready (Seq.slice whole 0 4) in
           let src = Ready (etypes_of ct_f32 false) in
           copy_complete_ok dst src /\
           replace_etypes whole 0 4 (state_etypes (complete_copy dst src)) == whole)
  = let whole = etypes_of ct_T true in
    let dst = Ready (Seq.slice whole 0 4) in
    let src = Ready (etypes_of ct_f32 false) in
    complete_copy_declared_stable dst src;
    Seq.lemma_eq_intro
      (replace_etypes whole 0 4 (state_etypes (complete_copy dst src))) whole
