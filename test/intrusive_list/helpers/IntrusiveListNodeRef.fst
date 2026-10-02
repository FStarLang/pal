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
   permission operations for a whole struct. That is a real gap, noted in
   palow.md; for one struct with two pointer fields and no padding it is
   fifteen lines, so it is not worth blocking this port on. *)

open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
#lang-pulse

module T = FStar.Tactics
module N = Struct_list_node

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
  unfold N.struct_list_node_pts_to r p (reveal v);
  ptr_share (r +! N.struct_list_node_offsetof_next);
  ptr_share (r +! N.struct_list_node_offsetof_prev);
  (* The node has no padding, so its padding slprop is `emp` and the two
     halves come from nothing. A struct with real padding would need
     `mem_share` here, and would fail to typecheck until it got it. *)
  unfold N.struct_list_node_padding r p;
  fold N.struct_list_node_padding r (p /. 2.0R);
  fold N.struct_list_node_padding r (p /. 2.0R);
  fold N.struct_list_node_pts_to r (p /. 2.0R) (reveal v);
  fold N.struct_list_node_pts_to r (p /. 2.0R) (reveal v);
}

[@@allow_ambiguous]
ghost fn gather (r: ptr) (#x0 #x1: erased N.struct_list_node) (#p0 #p1: perm)
  requires pts_to r #p0 x0
  requires pts_to r #p1 x1
  ensures  pts_to r #(p0 +. p1) x0
  ensures  pure (reveal x0 == reveal x1)
{
  unfold N.struct_list_node_pts_to r p0 (reveal x0);
  unfold N.struct_list_node_pts_to r p1 (reveal x1);
  ptr_gather (r +! N.struct_list_node_offsetof_next);
  ptr_gather (r +! N.struct_list_node_offsetof_prev);
  unfold N.struct_list_node_padding r p0;
  unfold N.struct_list_node_padding r p1;
  fold N.struct_list_node_padding r (p0 +. p1);
  fold N.struct_list_node_pts_to r (p0 +. p1) (reveal x0);
}

ghost fn pts_to_perm_bound (#p: perm) (r: ptr) (#v: N.struct_list_node)
  preserves pts_to r #p v
  ensures   pure (p <=. 1.0R)
{
  N.struct_list_node_focus_next r;
  ptr_reveal (r +! N.struct_list_node_offsetof_next);
  with b. assert (mem_pts_to (r +! N.struct_list_node_offsetof_next) p b);
  mem_pts_to_perm_bound (r +! N.struct_list_node_offsetof_next);
  ptr_conceal (r +! N.struct_list_node_offsetof_next) #p #b #(v.N.fld_next);
  N.struct_list_node_unfocus_read_next r;
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
   points-to hands over one scalar points-to per field -- so the residual is
   just the padding, which for this struct is nothing at all.
   --------------------------------------------------------------------------- *)

unfold let next_field (r: ptr) : ptr = r +! N.struct_list_node_offsetof_next
unfold let prev_field (r: ptr) : ptr = r +! N.struct_list_node_offsetof_prev

(* A field holds a node address, so its points-to is the pointer one rather
   than the node one: the shim is monomorphic and there are two types here. *)
unfold let pts_to_ref ([@@@mkey] r: ptr) (#[T.exact (`1.0R)] p: perm)
                      (v: ptr) : slprop =
  ptr_pts_to r p v

unfold let residual (r: ptr) (p: perm) : slprop =
  N.struct_list_node_padding r p

ghost fn open_node (r: ptr) (#p: perm) (v: N.struct_list_node)
  requires pts_to r #p v
  ensures  residual r p
  ensures  pts_to_ref (next_field r) #p v.N.fld_next
  ensures  pts_to_ref (prev_field r) #p v.N.fld_prev
{
  unfold N.struct_list_node_pts_to r p v;
}

ghost fn close_node (r: ptr) (#p: perm) (v_next v_prev: ptr)
  requires residual r p
  requires pts_to_ref (next_field r) #p v_next
  requires pts_to_ref (prev_field r) #p v_prev
  ensures  pts_to r #p ({ N.fld_next = v_next; N.fld_prev = v_prev })
{
  fold N.struct_list_node_pts_to r p ({ N.fld_next = v_next; N.fld_prev = v_prev });
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
