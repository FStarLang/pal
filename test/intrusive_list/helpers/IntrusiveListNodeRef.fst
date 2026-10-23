module IntrusiveListNodeRef

(* A `Pulse.Lib.Reference`-shaped view of a Palow pointer to a list node.

   The intrusive-list theory in this directory is about six thousand lines and
   says almost nothing about the memory model: it needs a node address, a
   points-to for it, and the fractional-permission operations. Under the
   current model that is `Pulse.Lib.Reference`; under Palow it is the
   `struct_list_node_*` surface the emitter generates. Rather than rewrite the
   theory, this module presents the second in the shape of the first, so that
   each ported helper differs from its original in its `module R = ...` line
   and nothing else.

   Two things are worth noticing about what is being shimmed. A reference is
   polymorphic and a Palow pointer is not -- a points-to there is per type,
   because it has to say how the bytes are laid out -- so `ref` ignores its
   argument and `pts_to` is fixed at the node type. And the sharing operations
   are written out here rather than taken from the model: Palow gives every
   scalar `share` and `gather`, but nothing assembles those into the
   permission operations for a whole struct. The shim instead reveals the
   actual indexed bytes, shares or gathers those, and restores the same
   structural view. *)

open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
#lang-pulse

module T = FStar.Tactics
module N = Struct_list_node
module ET = Pulse.Lib.C.Palow.Etype
module Rel = Pulse.Lib.C.Palow.Effective.Relation
module Seq = FStar.Seq

(* The type argument is what a reference carries and an address does not. *)
unfold let ref ([@@@unused] a: Type0) = ptr

(* `null` is in scope unqualified in every helper and resolves to the
   reference one through `open Pulse`, so the shim shadows it. *)
unfold let null : ptr = Pulse.Lib.C.Palow.Ptr.null

unfold let pts_to ([@@@mkey] r: ptr) (#[T.exact (`1.0R)] p: perm)
                  (v: N.struct_list_node) : slprop =
  N.struct_list_node_pts_to r p v

unfold let pts_to_uninit ([@@@mkey] r: ptr) : slprop =
  N.struct_list_node_pts_to_uninit r

ghost fn share (r: ptr) (#v: erased N.struct_list_node) (#p: perm)
  requires pts_to r #p v
  ensures  pts_to r #(p /. 2.0R) v ** pts_to r #(p /. 2.0R) v
{
  N.struct_list_node_reveal r #p #(reveal v);
  with b e. assert (mem_pts_to_at r p b e);
  mem_share_at r #p #b #e;
  N.struct_list_node_conceal r #(p /. 2.0R) #b #(reveal v) #e;
  N.struct_list_node_conceal r #(p /. 2.0R) #b #(reveal v) #e;
}

[@@allow_ambiguous]
ghost fn gather (r: ptr) (#x0 #x1: erased N.struct_list_node) (#p0 #p1: perm)
  requires pts_to r #p0 x0
  requires pts_to r #p1 x1
  ensures  pts_to r #(p0 +. p1) x0
  ensures  pure (reveal x0 == reveal x1)
{
  N.struct_list_node_reveal r #p0 #(reveal x0);
  with b0 e0. assert (mem_pts_to_at r p0 b0 e0);
  N.struct_list_node_reveal r #p1 #(reveal x1);
  with b1 e1. assert (mem_pts_to_at r p1 b1 e1);
  mem_gather_at r #p0 #p1 #b0 #b1 #e0 #e1;
  ptr_repr_injective (reveal x0).N.fld_next (reveal x1).N.fld_next (slice b0 0 8);
  ptr_repr_injective (reveal x0).N.fld_prev (reveal x1).N.fld_prev (slice b0 8 16);
  N.struct_list_node_conceal r #(p0 +. p1) #b0 #(reveal x0) #e0;
}

ghost fn pts_to_perm_bound (#p: perm) (r: ptr) (#v: N.struct_list_node)
  preserves pts_to r #p v
  ensures   pure (p <=. 1.0R)
{
  N.struct_list_node_reveal r #p #v;
  with b e. assert (mem_pts_to_at r p b e);
  mem_pts_to_at_perm_bound r;
  N.struct_list_node_conceal r #p #b #v #e;
}

ghost fn pts_to_not_null (#p: perm) (r: ptr) (#v: N.struct_list_node)
  preserves pts_to r #p v
  ensures   pure (not (is_null r))
{
  N.struct_list_node_pts_to_not_null r;
}

(* ---------------------------------------------------------------------------
   Opening a node into its fields

   `IntrusiveListValidate` reads a node's two links without giving up the node,
   which under the current model is what the `$unfold`/`$fold` antiquotations
   produce: a residual slprop standing for the rest of the object, and a
   *reference to each field*. Palow says the same thing more directly -- a
   field's address is the object's address plus its offset, and unfolding the
   points-to can lend a public read-only fraction per field. The residual
   keeps the other half of the whole node; closing uses byte/index agreement
   rather than guessing its original metadata.
   --------------------------------------------------------------------------- *)

unfold let next_field (r: ptr) : ptr = r +! N.struct_list_node_offsetof_next
unfold let prev_field (r: ptr) : ptr = r +! N.struct_list_node_offsetof_prev

(* The field loan uses half the requested permission. It is read-only even
   when the original node is held at full permission. *)
unfold let pts_to_ref ([@@@mkey] r: ptr) (#[T.exact (`1.0R)] p: perm)
                      (v: ptr) : slprop =
  ptr_pts_to r (p /. 2.0R) v

unfold let residual (r: ptr) (p: perm) : slprop =
  exists* v. N.struct_list_node_pts_to r (p /. 2.0R) v

ghost fn open_node (r: ptr) (#p: perm) (v: N.struct_list_node)
  requires pts_to r #p v
  ensures  residual r p
  ensures  pts_to_ref (next_field r) #p v.N.fld_next
  ensures  pts_to_ref (prev_field r) #p v.N.fld_prev
{
  N.struct_list_node_reveal r #p #v;
  with b e. assert (mem_pts_to_at r p b e);
  N.struct_list_node_view_fields ();
  Rel.view_read_ok_slice e N.struct_list_node_ctype 0 ptr_ctype;
  Rel.view_read_ok_slice e N.struct_list_node_ctype 8 ptr_ctype;
  Rel.view_scalar (Seq.slice e 0 8) ET.SPtr;
  Rel.view_scalar (Seq.slice e 8 16) ET.SPtr;
  N.struct_list_node_field_aligned r;
  mem_share_at r #p #b #e;
  N.struct_list_node_conceal r #(p /. 2.0R) #b #v #e;
  fold residual r p;
  mem_split_at r 8sz;
  ptr_conceal r #(p /. 2.0R) #(slice b 0 8) #v.N.fld_next;
  rewrite (ptr_pts_to r (p /. 2.0R) v.N.fld_next)
    as (ptr_pts_to (next_field r) (p /. 2.0R) v.N.fld_next);
  ptr_conceal (prev_field r) #(p /. 2.0R) #(slice b 8 16) #v.N.fld_prev;
}

ghost fn close_node (r: ptr) (#p: perm) (v_next v_prev: ptr)
  requires residual r p
  requires pts_to_ref (next_field r) #p v_next
  requires pts_to_ref (prev_field r) #p v_prev
  ensures  pts_to r #p ({ N.fld_next = v_next; N.fld_prev = v_prev })
{
  unfold residual r p;
  with old. assert (N.struct_list_node_pts_to r (p /. 2.0R) old);
  N.struct_list_node_reveal r #(p /. 2.0R) #old;
  with b e. assert (mem_pts_to_at r (p /. 2.0R) b e);
  ptr_reveal (next_field r) #(p /. 2.0R) #v_next;
  with bn en. assert (mem_pts_to_at (next_field r) (p /. 2.0R) bn en);
  rewrite (mem_pts_to_at (next_field r) (p /. 2.0R) bn en)
    as (mem_pts_to_at r (p /. 2.0R) bn en);
  ptr_reveal (prev_field r) #(p /. 2.0R) #v_prev;
  with bp ep. assert (mem_pts_to_at (prev_field r) (p /. 2.0R) bp ep);
  mem_join_at r #(p /. 2.0R) #bn #bp #en #ep 8sz;
  mem_gather_at r #(p /. 2.0R) #(p /. 2.0R)
    #b #(append bn bp) #e #(Seq.append en ep);
  append_slice_left bn bp;
  append_slice_right bn bp;
  ptr_repr_injective old.N.fld_next v_next bn;
  ptr_repr_injective old.N.fld_prev v_prev bp;
  N.struct_list_node_conceal r #p #b
    #({ N.fld_next = v_next; N.fld_prev = v_prev }) #e;
}

(* Giving up on the value while keeping the storage. The current model spells
   this as an `intro`/`forget` pair over `MaybeUninit`; Palow generates it. *)
ghost fn forget (r: ptr) (#v: erased N.struct_list_node)
  requires pts_to r #1.0R v
  ensures  pts_to_uninit r
{
  N.struct_list_node_forget r;
}

(* Pointer equality is decidable and exact here, where the reference model
   offers it as an operation. *)
unfold let ref_eq (a b: ptr) : (r: bool { r <==> a == b }) = ptr_eq a b
