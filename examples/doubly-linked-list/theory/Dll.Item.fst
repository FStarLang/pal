module Dll.Item

open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes
open Pulse.Lib.C.Palow.Machine
#lang-pulse

module T = FStar.Tactics
module N = Struct_list_node
module I = Struct_item
module SZ = FStar.SizeT

unfold let item_unfolded (a: ptr) (p: perm) : slprop = I.struct_item_padding a p
unfold let item_value_1 (a: ptr) : ptr = a +! I.struct_item_offsetof_value
unfold let item_link_1 (a: ptr) : ptr = a +! I.struct_item_offsetof_link
unfold let item_container (a: ptr) : ptr = a -? I.struct_item_offsetof_link

unfold let item_value ([@@@mkey] a: ptr) (#[T.exact (`1.0R)] p: perm)
                      (v: Int32.t) : slprop =
  int32_t_pts_to (item_value_1 a) p v

unfold let item_link ([@@@mkey] a: ptr) (#[T.exact (`1.0R)] p: perm)
                    (v: N.struct_list_node) : slprop =
  N.struct_list_node_pts_to (item_link_1 a) p v

ghost fn item_unfold (a: ptr) (#p: perm) (v: I.struct_item)
  requires I.struct_item_pts_to a p v
  ensures pure (addr_of a + SZ.v I.struct_item_sizeof < pow2 64)
  ensures item_unfolded a p
  ensures item_value a #p v.I.fld_value
  ensures N.struct_list_node_pts_to (item_link_1 a) p v.I.fld_link
{
  I.struct_item_reveal a;
  with b. assert (mem_pts_to a p b ** pure (I.struct_item_repr v b));
  I.struct_item_repr_len v b;
  mem_pts_to_fits a;
  I.struct_item_conceal a #p #b #v;
  unfold I.struct_item_pts_to a p v;
}

ghost fn item_fold (a: ptr) (#p: perm) (value: Int32.t) (link: N.struct_list_node)
  requires item_unfolded a p
  requires item_value a #p value
  requires N.struct_list_node_pts_to (item_link_1 a) p link
  ensures I.struct_item_pts_to a p ({ I.fld_value = value; I.fld_link = link })
{
  fold I.struct_item_pts_to a p ({ I.fld_value = value; I.fld_link = link });
}

unfold let item_pts_to ([@@@mkey] a: ptr) (#[T.exact (`1.0R)] p: perm)
                       (v: I.struct_item) : slprop =
  I.struct_item_pts_to a p v

(* Container recovery must not underflow the address space. Whole-item
   ownership establishes this fact when splitting off its embedded link. *)
unfold let item_embedded (node: ptr) : prop =
  SZ.v I.struct_item_offsetof_link <= addr_of node
