module Pulse.Lib.C.Palow.Effective.View
(* Accessing a declared object through a pointer of another type.

   Converting the address of an `int` object to `unsigned` pointer type does
   not create a second object: dereferencing the result is an access to the bytes of `n`, at type `unsigned`. Whether that access is
   permitted is exactly 6.5p7, which `Etype.access_ok` already decides for each
   byte: the bytes of `n` are labelled `int`, and an `int` has an `unsigned`
   subobject at offset 0. So a view is a change of the *ownership predicate*
   over the same bytes and the same effective-type index, justified by
   `access_ok` and by the bytes also being a valid representation at the view
   type.

   Only same-size scalar views are offered. An aggregate view of a declared
   object that is not the object's own type (or its first member, which the
   emitter rewrites to a member path) is never licensed here, so a struct pun
   is rejected by the verifier rather than by the translator. *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes
open Pulse.Lib.C.Palow.Array
open Pulse.Lib.C.Palow.Encoding

module SZ = FStar.SizeT
module ET = Pulse.Lib.C.Palow.Etype
module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

(* The effective-type half of 6.5p7 for a view of the same width: an object of
   type `cs` has an accessible `cv` at offset 0. *)
let view_compatible (cs cv: ET.ctype) : bool =
  ET.TScalar? cs && ET.TScalar? cv && ET.csize cs = ET.csize cv && ET.access_ok cs 0 cv &&
  (* A view does not retype its object: through an `unsigned int` view of an
     `enum A`, an `enum B` is still not accessible. *)
  ET.compose_ok cs cv

let view_byte_ok (e: ET.etypes) (cs cv: ET.ctype) (k: nat)
  : Lemma (requires ET.read_ok e cs /\ view_compatible cs cv)
          (ensures  k < ET.elen e ==>
                    (match ET.eget e k with
                     | None -> True
                     | Some en -> b2t (ET.access_ok en.ty (en.off - k) cv)))
  = if k < ET.elen e then
      match ET.eget e k with
      | None -> ()
      | Some en -> ET.access_ok_trans en.ty (en.off - k) cs 0 cv

let view_read_ok (e: ET.etypes) (cs cv: ET.ctype)
  : Lemma (requires ET.read_ok e cs /\ view_compatible cs cv)
          (ensures  ET.read_ok e cv)
  = Classical.forall_intro (Classical.move_requires (view_byte_ok e cs cv))

(* The value half: every representation of a source value also represents some
   value of the view type. A trap representation -- a byte that is not 0 or 1
   seen as `bool` -- is where this fails. *)
let repr_view (#ts #tv: Type0) (rs: ts -> bytes -> prop) (rv: tv -> bytes -> prop) : prop =
  forall (x: ts) (b: bytes). rs x b ==> (exists (y: tv). rv y b)

let view_ok (#ts #tv: Type0) (cs: ET.ctype) (rs: ts -> bytes -> prop)
            (cv: ET.ctype) (rv: tv -> bytes -> prop) : prop =
  b2t (view_compatible cs cv) /\ repr_view rs rv

let choose (#tv: Type0) (rv: tv -> bytes -> prop) (b: bytes { exists (y: tv). rv y b })
  : GTot (y: tv { rv y b })
  = FStar.IndefiniteDescription.indefinite_description_ghost tv (fun y -> rv y b)

ghost fn elem_view (#ts #tv: Type0) (cs: ET.ctype) (rs: ts -> bytes -> prop)
                   (cv: ET.ctype) (rv: tv -> bytes -> prop) (a: ptr) (#p: perm) (#x: ts)
  requires elem_pts_to cs rs a p x
  requires pure (view_ok cs rs cv rv)
  ensures  exists* (y: tv). elem_pts_to cv rv a p y
{
  elem_reveal cs rs a;
  with b e. assert (mem_pts_to_at a p b e);
  view_read_ok e cs cv;
  let y = choose rv b;
  elem_conceal cv rv a #p #b #y #e;
}

(* A declared aggregate is never viewed at an unrelated type: the emitter only
   gets here when the view is neither the object's own type nor its first
   member, and that is 6.5p7 undefined behaviour. *)
let aggregate_view_ok (cs cv: ET.ctype) : bool =
  ET.TScalar? cs && ET.TScalar? cv && view_compatible cs cv

ghost fn aggregate_view (cs cv: ET.ctype)
  requires pure (aggregate_view_ok cs cv)
  ensures  emp
{
  ()
}

(* Same-width representation facts for the pairs `view_compatible` admits. *)

let repr_view_intro (#ts #tv: Type0) (rs: ts -> bytes -> prop) (rv: tv -> bytes -> prop)
                    (f: ts -> GTot tv)
                    (pf: (x: ts) -> (b: bytes) -> Lemma (requires rs x b) (ensures rv (f x) b))
  : Lemma (repr_view rs rv)
  = let aux (x: ts) (b: bytes) : Lemma (rs x b ==> (exists (y: tv). rv y b)) =
      Classical.move_requires (pf x) b
    in
    Classical.forall_intro_2 aux

let signed_of (w: pos) (v: nat { v < pow2 w }) : (s: int { -(pow2 (w - 1)) <= s /\ s < pow2 (w - 1) /\ to_bits w s == v }) =
  FStar.Math.Lemmas.pow2_double_sum (w - 1);
  if v < pow2 (w - 1) then v else v - pow2 w

let repr_int8_uint8 () : Lemma (repr_view int8_t_repr uint8_t_repr) =
  repr_view_intro int8_t_repr uint8_t_repr (fun x -> U8.uint_to_t (to_bits 8 (I8.v x))) (fun _ _ -> ())

let repr_uint8_int8 () : Lemma (repr_view uint8_t_repr int8_t_repr) =
  repr_view_intro uint8_t_repr int8_t_repr (fun x -> I8.int_to_t (signed_of 8 (U8.v x))) (fun _ _ -> ())

let repr_int16_uint16 () : Lemma (repr_view int16_t_repr uint16_t_repr) =
  repr_view_intro int16_t_repr uint16_t_repr (fun x -> U16.uint_to_t (to_bits 16 (I16.v x))) (fun _ _ -> ())

let repr_uint16_int16 () : Lemma (repr_view uint16_t_repr int16_t_repr) =
  repr_view_intro uint16_t_repr int16_t_repr (fun x -> I16.int_to_t (signed_of 16 (U16.v x))) (fun _ _ -> ())

let repr_int32_uint32 () : Lemma (repr_view int32_t_repr uint32_t_repr) =
  repr_view_intro int32_t_repr uint32_t_repr (fun x -> U32.uint_to_t (to_bits 32 (I32.v x))) (fun _ _ -> ())

let repr_uint32_int32 () : Lemma (repr_view uint32_t_repr int32_t_repr) =
  repr_view_intro uint32_t_repr int32_t_repr (fun x -> I32.int_to_t (signed_of 32 (U32.v x))) (fun _ _ -> ())

let repr_int64_uint64 () : Lemma (repr_view int64_t_repr uint64_t_repr) =
  repr_view_intro int64_t_repr uint64_t_repr (fun x -> U64.uint_to_t (to_bits 64 (I64.v x))) (fun _ _ -> ())

let repr_uint64_int64 () : Lemma (repr_view uint64_t_repr int64_t_repr) =
  repr_view_intro uint64_t_repr int64_t_repr (fun x -> I64.int_to_t (signed_of 64 (U64.v x))) (fun _ _ -> ())

let repr_llong_ullong () : Lemma (repr_view long_long_t_repr ulong_long_t_repr) =
  repr_view_intro long_long_t_repr ulong_long_t_repr (fun x -> U64.uint_to_t (to_bits 64 (I64.v x))) (fun _ _ -> ())

let repr_ullong_llong () : Lemma (repr_view ulong_long_t_repr long_long_t_repr) =
  repr_view_intro ulong_long_t_repr long_long_t_repr (fun x -> I64.int_to_t (signed_of 64 (U64.v x))) (fun _ _ -> ())

let repr_uint64_size_t () : Lemma (repr_view uint64_t_repr size_t_repr) =
  repr_view_intro uint64_t_repr size_t_repr (fun x -> SZ.uint64_to_sizet x) (fun _ _ -> ())

let repr_size_t_uint64 () : Lemma (repr_view size_t_repr uint64_t_repr) =
  repr_view_intro size_t_repr uint64_t_repr (fun x -> SZ.sizet_to_uint64 x) (fun _ _ -> ())

let repr_bool_int8 () : Lemma (repr_view bool_t_repr int8_t_repr) =
  repr_view_intro bool_t_repr int8_t_repr (fun x -> if x then 1y else 0y) (fun _ _ -> ())

let repr_bool_uint8 () : Lemma (repr_view bool_t_repr uint8_t_repr) =
  repr_view_intro bool_t_repr uint8_t_repr (fun x -> if x then 1uy else 0uy) (fun _ _ -> ())
