module IntrusiveListItemRefs

(* The same shim as `IntrusiveListNodeRef`, for the three client structures
   that embed a list node.

   Each client example opens its item into per-field references, reads or
   writes one of them, and folds it back; under the current model that is the
   `$unfold`/`$fold` antiquotations and the generated `__f_1` field-reference
   and `__f_container` recovery functions. Palow needs none of those as
   primitives -- a field's address is the object's plus an offset, recovering
   the container is the offset back, and opening the object is unfolding its
   points-to -- so what is left here is naming.

   Two differences are not just naming, and they are the interesting ones. A
   field address is computed rather than assumed, so `container (proj p) == p`
   is arithmetic with an SMT pattern instead of an axiom the emitter had to
   generate. And a points-to is per type, so the single polymorphic `R.pts_to`
   of the reference model becomes one definition per field -- which is the
   price of saying how the bytes are laid out. *)

open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.Array
open Pulse.Lib.C.Palow.CTypes
open Pulse.Lib.C.Palow.Machine
#lang-pulse

module T = FStar.Tactics
module N = Struct_list_node
module I1 = Struct_item
module I2 = Struct_item2
module I3 = Struct_item3
module Seq = FStar.Seq
module SZ = FStar.SizeT

(* --- struct item: value, link ------------------------------------------- *)

unfold let item_unfolded (a: ptr) (p: perm) : slprop = I1.struct_item_padding a p
unfold let item_value_1 (a: ptr) : ptr = a +! I1.struct_item_offsetof_value
unfold let item_link_1 (a: ptr) : ptr = a +! I1.struct_item_offsetof_link
unfold let item_container (a: ptr) : ptr = a -? I1.struct_item_offsetof_link

unfold let item_value ([@@@mkey] a: ptr) (#[T.exact (`1.0R)] p: perm)
                      (v: Int32.t) : slprop =
  int32_t_pts_to (item_value_1 a) p v

(* The link is a node, so this is the node points-to at the field's
   address -- named here only so that every field reads alike. *)
unfold let item_link ([@@@mkey] a: ptr) (#[T.exact (`1.0R)] p: perm)
                    (v: N.struct_list_node) : slprop =
  N.struct_list_node_pts_to (item_link_1 a) p v

ghost fn item_unfold (a: ptr) (#p: perm) (v: I1.struct_item)
  requires I1.struct_item_pts_to a p v
  ensures  item_unfolded a p
  ensures  item_value a #p v.I1.fld_value
  ensures  N.struct_list_node_pts_to (item_link_1 a) p v.I1.fld_link
{
  unfold I1.struct_item_pts_to a p v;
}

ghost fn item_fold (a: ptr) (#p: perm) (v_value: Int32.t) (v_link: N.struct_list_node)
  requires item_unfolded a p
  requires item_value a #p v_value
  requires N.struct_list_node_pts_to (item_link_1 a) p v_link
  ensures  I1.struct_item_pts_to a p ({ I1.fld_value = v_value; I1.fld_link = v_link })
{
  fold I1.struct_item_pts_to a p ({ I1.fld_value = v_value; I1.fld_link = v_link });
}

(* --- struct item2: priority, used, samples, processed, link ------------- *)

unfold let item2_unfolded (a: ptr) (p: perm) : slprop = I2.struct_item2_padding a p
unfold let item2_priority_1 (a: ptr) : ptr = a +! I2.struct_item2_offsetof_priority
unfold let item2_used_1 (a: ptr) : ptr = a +! I2.struct_item2_offsetof_used
unfold let item2_samples_1 (a: ptr) : ptr = a +! I2.struct_item2_offsetof_samples
unfold let item2_processed_1 (a: ptr) : ptr = a +! I2.struct_item2_offsetof_processed
unfold let item2_link_1 (a: ptr) : ptr = a +! I2.struct_item2_offsetof_link
unfold let item2_container (a: ptr) : ptr = a -? I2.struct_item2_offsetof_link

unfold let samples_t = (s: Seq.seq UInt32.t { Seq.length s == 4 })

unfold let item2_priority ([@@@mkey] a: ptr) (#[T.exact (`1.0R)] p: perm)
                          (v: Int32.t) : slprop =
  int32_t_pts_to (item2_priority_1 a) p v
unfold let item2_used ([@@@mkey] a: ptr) (#[T.exact (`1.0R)] p: perm)
                      (v: UInt32.t) : slprop =
  uint32_t_pts_to (item2_used_1 a) p v
unfold let item2_samples ([@@@mkey] a: ptr) (#[T.exact (`1.0R)] p: perm)
                         (v: samples_t) : slprop =
  array_pts_to uint32_t_repr 4 (item2_samples_1 a) p v
unfold let item2_processed ([@@@mkey] a: ptr) (#[T.exact (`1.0R)] p: perm)
                           (v: ptr) : slprop =
  ptr_pts_to (item2_processed_1 a) p v

(* The link is a node, so this is the node points-to at the field's
   address -- named here only so that every field reads alike. *)
unfold let item2_link ([@@@mkey] a: ptr) (#[T.exact (`1.0R)] p: perm)
                    (v: N.struct_list_node) : slprop =
  N.struct_list_node_pts_to (item2_link_1 a) p v

ghost fn item2_unfold (a: ptr) (#p: perm) (v: I2.struct_item2)
  requires I2.struct_item2_pts_to a p v
  ensures  item2_unfolded a p
  ensures  item2_priority a #p v.I2.fld_priority
  ensures  item2_used a #p v.I2.fld_used
  ensures  item2_samples a #p v.I2.fld_samples
  ensures  item2_processed a #p v.I2.fld_processed
  ensures  N.struct_list_node_pts_to (item2_link_1 a) p v.I2.fld_link
{
  unfold I2.struct_item2_pts_to a p v;
}

ghost fn item2_fold (a: ptr) (#p: perm) (v_priority: Int32.t) (v_used: UInt32.t)
                    (v_samples: samples_t) (v_processed: ptr)
                    (v_link: N.struct_list_node)
  requires item2_unfolded a p
  requires item2_priority a #p v_priority
  requires item2_used a #p v_used
  requires item2_samples a #p v_samples
  requires item2_processed a #p v_processed
  requires N.struct_list_node_pts_to (item2_link_1 a) p v_link
  ensures  I2.struct_item2_pts_to a p ({ I2.fld_priority = v_priority;
                                         I2.fld_used = v_used;
                                         I2.fld_samples = v_samples;
                                         I2.fld_processed = v_processed;
                                         I2.fld_link = v_link })
{
  fold I2.struct_item2_pts_to a p ({ I2.fld_priority = v_priority;
                                     I2.fld_used = v_used;
                                     I2.fld_samples = v_samples;
                                     I2.fld_processed = v_processed;
                                     I2.fld_link = v_link });
}

(* --- struct item3: ready, link ------------------------------------------ *)

unfold let item3_unfolded (a: ptr) (p: perm) : slprop = I3.struct_item3_padding a p
unfold let item3_ready_1 (a: ptr) : ptr = a +! I3.struct_item3_offsetof_ready
unfold let item3_link_1 (a: ptr) : ptr = a +! I3.struct_item3_offsetof_link
unfold let item3_container (a: ptr) : ptr = a -? I3.struct_item3_offsetof_link

unfold let item3_ready ([@@@mkey] a: ptr) (#[T.exact (`1.0R)] p: perm)
                       (v: bool) : slprop =
  bool_t_pts_to (item3_ready_1 a) p v

(* The link is a node, so this is the node points-to at the field's
   address -- named here only so that every field reads alike. *)
unfold let item3_link ([@@@mkey] a: ptr) (#[T.exact (`1.0R)] p: perm)
                    (v: N.struct_list_node) : slprop =
  N.struct_list_node_pts_to (item3_link_1 a) p v

ghost fn item3_unfold (a: ptr) (#p: perm) (v: I3.struct_item3)
  requires I3.struct_item3_pts_to a p v
  ensures  item3_unfolded a p
  ensures  item3_ready a #p v.I3.fld_ready
  ensures  N.struct_list_node_pts_to (item3_link_1 a) p v.I3.fld_link
{
  unfold I3.struct_item3_pts_to a p v;
}

ghost fn item3_fold (a: ptr) (#p: perm) (v_ready: bool) (v_link: N.struct_list_node)
  requires item3_unfolded a p
  requires item3_ready a #p v_ready
  requires N.struct_list_node_pts_to (item3_link_1 a) p v_link
  ensures  I3.struct_item3_pts_to a p ({ I3.fld_ready = v_ready; I3.fld_link = v_link })
{
  fold I3.struct_item3_pts_to a p ({ I3.fld_ready = v_ready; I3.fld_link = v_link });
}

(* --- whole-object points-to -------------------------------------------- *)

(* `IntrusiveListNodeRef.pts_to` is fixed at the node type, which is all the
   generic list theory ever needs. A client example also owns the enclosing
   item, and one cell beside it, so those get names here. Making the shim's
   `pts_to` dispatch on the value's type instead was tried and abandoned: the
   theory writes `with v. assert (R.pts_to cur #p v)` in a dozen places, where
   `v` has no annotation and a monomorphic points-to is what determines it. *)

unfold let item_pts_to ([@@@mkey] a: ptr) (#[T.exact (`1.0R)] p: perm)
                       (v: I1.struct_item) : slprop =
  I1.struct_item_pts_to a p v
unfold let item2_pts_to ([@@@mkey] a: ptr) (#[T.exact (`1.0R)] p: perm)
                        (v: I2.struct_item2) : slprop =
  I2.struct_item2_pts_to a p v
unfold let item3_pts_to ([@@@mkey] a: ptr) (#[T.exact (`1.0R)] p: perm)
                        (v: I3.struct_item3) : slprop =
  I3.struct_item3_pts_to a p v
unfold let u32_pts_to ([@@@mkey] a: ptr) (#[T.exact (`1.0R)] p: perm)
                      (v: UInt32.t) : slprop =
  uint32_t_pts_to a p v

unfold let item_pts_to_uninit (a: ptr) : slprop = I1.struct_item_pts_to_uninit a
unfold let item2_pts_to_uninit (a: ptr) : slprop = I2.struct_item2_pts_to_uninit a
unfold let item3_pts_to_uninit (a: ptr) : slprop = I3.struct_item3_pts_to_uninit a

(* --- the link really is a link ------------------------------------------ *)

(* Recovering the item from its link field is `container_of`, and it only
   round-trips if the offset is there to take back: `(a -? n) +! n == a` needs
   `n <= addr_of a`. The current model assumes both directions of the round
   trip outright, as generated axioms about opaque projection and container
   functions. Palow computes both, so one direction is arithmetic and the
   other needs its premise stated -- and stating it is no loss, because it is
   exactly the fact that makes the recovery meaningful: this address is a link
   field inside an item, rather than any address at all.

   It belongs in the payload predicate, which is where "this node is one of
   mine" is already said. *)

unfold let item_embedded (node: ptr) : prop =
  SZ.v I1.struct_item_offsetof_link <= addr_of node
unfold let item2_embedded (node: ptr) : prop =
  SZ.v I2.struct_item2_offsetof_link <= addr_of node
unfold let item3_embedded (node: ptr) : prop =
  SZ.v I3.struct_item3_offsetof_link <= addr_of node
