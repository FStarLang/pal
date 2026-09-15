module IntrusiveListRemove
open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module R = Pulse.Lib.Reference
module N = Struct_list_node
module L = IntrusiveList
module X = IntrusiveListIndexed

let inv (#a: Type0) (p: L.ipayload a) (m: X.matcher a) (head pos: L.lref)
        (es: X.entries a) : slprop =
  exists* (seen back: X.entries a).
    X.split p head pos (X.without m seen) back **
    X.detached p (X.matching m seen) **
    pure (seen @ back == es)

let mid (#a: Type0) (p: L.ipayload a) (m: X.matcher a) (head pos: L.lref)
        (es: X.entries a) (description: a) (v: N.struct_list_node) : slprop =
  exists* (seen back: X.entries a).
    X.cursor_rest p head pos (X.without m seen) description back v **
    X.detached p (X.matching m seen) **
    pure (L.lnext v == L.first_or head (L.cells_of back)) **
    pure (seen @ ((pos, description) :: back) == es)

(* The saved successor is fixed before deletion; payloads are merely framed. *)
let pending (#a: Type0) (p: L.ipayload a) (m: X.matcher a)
            (head pos next: L.lref) (es: X.entries a) (description: a)
            (seen back: X.entries a) : slprop =
  L.ipayload_of p (X.without m seen @ ((pos, description) :: back)) **
  X.detached p (X.matching m seen) **
  pure (seen @ ((pos, description) :: back) == es) **
  pure (next == L.first_or head (L.cells_of back)) **
  pure (m pos description)

ghost
fn start (#a: Type0) (p: L.ipayload a) (m: X.matcher a) (head pos: L.lref)
         (es: X.entries a) (#hv: N.struct_list_node)
  requires R.pts_to head hv ** X.head_rest p head es hv ** pure (pos == L.lnext hv)
  ensures inv p m head pos es
{
  X.cursor_start p head pos es;
  fold (X.detached p []);
  rewrite (X.split p head pos [] es) as (X.split p head pos (X.without m []) es);
  rewrite (X.detached p []) as (X.detached p (X.matching m []));
  fold (inv p m head pos es);
}

ghost
fn expose (#a: Type0) (p: L.ipayload a) (m: X.matcher a) (head pos: L.lref)
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
fn keep (#a: Type0) (p: L.ipayload a) (m: X.matcher a) (head pos next: L.lref)
        (es: X.entries a) (#description: a) (#v: N.struct_list_node)
  requires R.pts_to pos v ** p pos description ** mid p m head pos es description v **
    pure (next == L.lnext v) ** pure (not (m pos description))
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
  rewrite (X.split p head (L.lnext v) (X.without m seen @ [(pos, description)]) back)
    as (X.split p head next (X.without m (seen @ [(pos, description)])) back);
  rewrite (X.detached p (X.matching m seen))
    as (X.detached p (X.matching m (seen @ [(pos, description)])));
  fold (inv p m head next es);
}

ghost
fn drop_prepare (#a: Type0) (p: L.ipayload a) (m: X.matcher a)
                (head pos next: L.lref) (es: X.entries a)
                (#description: a) (#v: N.struct_list_node)
  requires R.pts_to pos v ** p pos description ** mid p m head pos es description v **
    pure (next == L.lnext v) ** pure (m pos description)
  ensures exists* (seen back: X.entries a).
    L.is_list_ring_with L.emp_pl head 1.0R
      (L.cells_of (X.without m seen) @ (pos :: L.cells_of back)) **
    pending p m head pos next es description seen back
{
  unfold (mid p m head pos es description v);
  with seen back.
    assert (X.cursor_rest p head pos (X.without m seen) description back v);
  X.cursor_restore p head pos (X.without m seen) description back;
  X.split_close p head pos (X.without m seen) ((pos, description) :: back);
  X.ops_open_at p head (X.without m seen) (pos, description) back;
  fold (pending p m head pos next es description seen back);
}

ghost
fn drop_finish (#a: Type0) (p: L.ipayload a) (m: X.matcher a)
               (head pos next: L.lref) (es: X.entries a)
               (#description: a) (#seen #back: X.entries a) (#link: N.struct_list_node)
  requires L.is_list_ring_with L.emp_pl head 1.0R
      (L.cells_of (X.without m seen) @ L.cells_of back) **
    R.pts_to pos link ** L.emp_pl pos **
    pending p m head pos next es description seen back
  ensures inv p m head next es
{
  unfold (pending p m head pos next es description seen back);
  rewrite (L.emp_pl pos) as emp;
  L.ipayload_of_remove p (X.without m seen) back pos description;
  X.ops_close_remove p head (X.without m seen) back;
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
fn finish (#a: Type0) (p: L.ipayload a) (m: X.matcher a) (head pos: L.lref)
          (es: X.entries a)
  requires inv p m head pos es ** pure (pos == head)
  ensures L.is_list_ring_ix p head 1.0R (X.without m es) **
    X.detached p (X.matching m es) **
    pure (X.no_match m (X.without m es)) **
    pure (X.first_match_entry m (X.without m es) == None) **
    pure (X.first_match m (X.without m es) == null)
{
  unfold (inv p m head pos es);
  with seen back. assert (X.split p head pos (X.without m seen) back);
  X.split_facts p head pos (X.without m seen) back;
  FStar.List.Tot.append_l_nil seen;
  FStar.List.Tot.append_l_nil (X.without m seen);
  X.split_close p head pos (X.without m seen) back;
  rewrite (L.is_list_ring_ix p head 1.0R (X.without m seen @ back))
    as (L.is_list_ring_ix p head 1.0R (X.without m es));
  rewrite (X.detached p (X.matching m seen))
    as (X.detached p (X.matching m es));
  X.filtered_no_match m es;
  X.first_match_skip m (X.without m es) [];
  FStar.List.Tot.append_l_nil (X.without m es);
}
