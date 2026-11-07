module IntrusiveListRemove

(* Stable filtering keeps survivor order and collects every removed node/payload.
   The saved successor allows traversal to continue after unlinking the current node. *)

open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module R = IntrusiveListNodeRef
module N = Struct_list_node
module X = IntrusiveListIndexed
module C = IntrusiveListContext

let inv (#a: Type0) (p: X.ipayload a) (m: X.matcher a) (head pos: X.lref)
        (es: X.entries a) : slprop =
  exists* (seen back: X.entries a).
    X.split p head pos (X.without m seen) back **
    X.detached p (X.matching m seen) **
    pure (seen @ back == es)

let mid (#a: Type0) (p: X.ipayload a) (m: X.matcher a) (head pos: X.lref)
        (es: X.entries a) (description: a) (v: N.struct_list_node) : slprop =
  exists* (seen back: X.entries a).
    X.cursor_rest p head pos (X.without m seen) description back v **
    X.detached p (X.matching m seen) **
    pure (X.lnext v == X.first_or head back) **
    pure (seen @ ((pos, description) :: back) == es)

(* Deletion consumes the ring; previously detached entries remain framed. *)
let pending (#a: Type0) (p: X.ipayload a) (m: X.matcher a)
            (head pos next: X.lref) (es: X.entries a) (description: a)
            (seen back: X.entries a) : slprop =
  X.detached p (X.matching m seen) **
  pure (seen @ ((pos, description) :: back) == es) **
  pure (next == X.first_or head back) **
  pure (m pos description)

unfold let removal_context (#a: Type0) (p: X.ipayload a) (m: X.matcher a)
                    (head pos: X.lref) (description: a)
                    (seen back: X.entries a) : GTot C.cut = {
  model = {
    description_type = a;
    resource = p;
    entries = X.without m seen @ ((pos, description) :: back);
  };
  head = head;
  front = X.without m seen;
  back = back;
  description = description;
}

ghost
fn start (#a: Type0) (p: X.ipayload a) (m: X.matcher a) (head pos: X.lref)
         (es: X.entries a) (#hv: N.struct_list_node)
  requires R.pts_to head hv ** X.head_rest p head es hv ** pure (pos == X.lnext hv)
  ensures inv p m head pos es
{
  X.cursor_start p head pos es;
  fold (X.detached p []);
  rewrite (X.split p head pos [] es) as (X.split p head pos (X.without m []) es);
  rewrite (X.detached p []) as (X.detached p (X.matching m []));
  fold (inv p m head pos es);
}

ghost
fn expose (#a: Type0) (p: X.ipayload a) (m: X.matcher a) (head pos: X.lref)
          (es: X.entries a)
  requires inv p m head pos es ** pure (pos =!= head)
  ensures exists* (description: a) (v: N.struct_list_node).
    R.pts_to pos v ** p pos description ** mid p m head pos es description v
{
  unfold (inv p m head pos es);
  with seen back. assert (X.split p head pos (X.without m seen) back);
  X.split_facts p head pos (X.without m seen) back;
  let e = Cons?.hd back;
  let rest = Cons?.tl back;
  rewrite (X.split p head pos (X.without m seen) back)
    as (X.split p head pos (X.without m seen) (e :: rest));
  X.cursor_expose p head pos (X.without m seen) e rest;
  with v. assert (R.pts_to pos v);
  fold (mid p m head pos es (snd e) v);
}

ghost
fn keep (#a: Type0) (p: X.ipayload a) (m: X.matcher a) (head pos next: X.lref)
        (es: X.entries a) (#description: a) (#v: N.struct_list_node)
  requires R.pts_to pos v ** p pos description ** mid p m head pos es description v **
    pure (next == X.lnext v) ** pure (not (m pos description))
  ensures inv p m head next es
{
  unfold (mid p m head pos es description v);
  with seen back.
    assert (X.cursor_rest p head pos (X.without m seen) description back v);
  X.cursor_advance p head pos (X.without m seen) description back;
  X.without_append m seen [(pos, description)];
  X.matching_append m seen [(pos, description)];
  FStar.List.Tot.append_l_nil (X.matching m seen);
  FStar.List.Tot.Properties.append_assoc seen [(pos, description)] back;
  rewrite (X.split p head (X.lnext v) (X.without m seen @ [(pos, description)]) back)
    as (X.split p head next (X.without m (seen @ [(pos, description)])) back);
  rewrite (X.detached p (X.matching m seen))
    as (X.detached p (X.matching m (seen @ [(pos, description)])));
  fold (inv p m head next es);
}

ghost
fn drop_prepare (#a: Type0) (p: X.ipayload a) (m: X.matcher a)
                (head pos next: X.lref) (es: X.entries a)
                (#description: a) (#v: N.struct_list_node)
  requires R.pts_to pos v ** p pos description ** mid p m head pos es description v **
    pure (next == X.lnext v) ** pure (m pos description)
  ensures exists* (seen back: X.entries a).
    C.remove_pre (removal_context p m head pos description seen back) pos **
    pending p m head pos next es description seen back
{
  unfold (mid p m head pos es description v);
  with seen back.
    assert (X.cursor_rest p head pos (X.without m seen) description back v);
  X.cursor_restore p head pos (X.without m seen) description back;
  X.split_close p head pos (X.without m seen) ((pos, description) :: back);
  C.prepare_ring (removal_context p m head pos description seen back).model head;
  fold (C.remove_pre (removal_context p m head pos description seen back) pos);
  fold (pending p m head pos next es description seen back);
}

ghost
fn drop_finish (#a: Type0) (p: X.ipayload a) (m: X.matcher a)
               (head pos next: X.lref) (es: X.entries a)
               (#description: a) (#seen #back: X.entries a) (#empty: bool)
  requires C.remove_post (removal_context p m head pos description seen back) pos empty **
    pending p m head pos next es description seen back
  ensures inv p m head next es
{
  unfold (pending p m head pos next es description seen back);
  unfold (C.remove_post (removal_context p m head pos description seen back) pos empty);
  X.detached_snoc p (X.matching m seen) pos description;
  X.without_append m seen [(pos, description)];
  X.matching_append m seen [(pos, description)];
  FStar.List.Tot.append_l_nil (X.without m seen);
  FStar.List.Tot.Properties.append_assoc seen [(pos, description)] back;
  X.split_open p head (X.without m seen) back;
  with cur. assert (X.split p head cur (X.without m seen) back);
  rewrite (X.split p head cur (X.without m seen) back)
    as (X.split p head next (X.without m (seen @ [(pos, description)])) back);
  rewrite (X.detached p (X.matching m seen @ [(pos, description)]))
    as (X.detached p (X.matching m (seen @ [(pos, description)])));
  fold (inv p m head next es);
}

ghost
fn finish (#a: Type0) (p: X.ipayload a) (m: X.matcher a) (head pos: X.lref)
          (es: X.entries a)
  requires inv p m head pos es ** pure (pos == head)
  ensures X.is_list_ring_ix p head 1.0R (X.without m es) **
    X.detached p (X.matching m es) **
    pure (X.no_match m (X.without m es)) **
    pure (X.first_match_entry m (X.without m es) == None) **
    pure (X.first_match m (X.without m es) == R.null)
{
  unfold (inv p m head pos es);
  with seen back. assert (X.split p head pos (X.without m seen) back);
  X.split_facts p head pos (X.without m seen) back;
  FStar.List.Tot.append_l_nil seen;
  FStar.List.Tot.append_l_nil (X.without m seen);
  X.split_close p head pos (X.without m seen) back;
  rewrite (X.is_list_ring_ix p head 1.0R (X.without m seen @ back))
    as (X.is_list_ring_ix p head 1.0R (X.without m es));
  rewrite (X.detached p (X.matching m seen))
    as (X.detached p (X.matching m es));
  X.filtered_no_match m es;
  X.first_match_skip m (X.without m es) [];
  FStar.List.Tot.append_l_nil (X.without m es);
}
