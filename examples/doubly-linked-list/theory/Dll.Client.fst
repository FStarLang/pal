module Dll.Client

(* Concrete integer payload ownership and client postconditions. *)

open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module R = IntrusiveListNodeRef
module IR = Dll.Item
module N = Struct_list_node
module I = Struct_item
module Q = IntrusiveListItems
module X = IntrusiveListIndexed

(* Concrete payload ownership belongs here; reusable list helpers do not import this module. *)
unfold let entries = X.entries Int32.t
unfold let item_ref = R.ref I.struct_item
(* Concrete item ownership and its embedded link's address. *)
unfold let item_pts_to (r: item_ref) (v: I.struct_item) : slprop = IR.item_pts_to r v

unfold let item_link (r: item_ref) : X.lref = IR.item_link_1 r

unfold let owner (node: X.lref) : item_ref =
  IR.item_container node

let item_ipl : X.ipayload Int32.t =
  fun node value ->
    IR.item_unfolded (owner node) 1.0R **
    IR.item_value ((owner node)) value **
    pure (IR.item_embedded node)

unfold let item_record (value: Int32.t) (link: N.struct_list_node) =
  { I.fld_value = value; I.fld_link = link; }

let matches_value (key: Int32.t) (_node: X.lref) (value: Int32.t) : GTot bool =
  value == key

let value_le (x y: Int32.t) : GTot bool =
  Int32.v x <= Int32.v y

let value_order () : Lemma (X.total_preorder value_le) = ()

ghost
(* The payload owns the item apart from its link, and the list owns the link;
   Palow reads `item->value` from the item as a whole, so opening the payload
   means joining the two back up rather than handing out a field reference. *)
fn value_open (node: X.lref) (item: item_ref) (#value: Int32.t)
              (#link: N.struct_list_node)
  requires item_ipl node value ** R.pts_to node link **
    pure (item == owner node)
  ensures IR.item_pts_to item (item_record value link) **
    (* Carried out so that closing the payload again can recover the item
       from its link; see `Dll.Item.item_embedded`. *)
    pure (IR.item_embedded node)
{
  unfold (item_ipl node value);
  rewrite (R.pts_to node link) as (IR.item_link ((owner node)) link);
  IR.item_fold (owner node) value link;
  rewrite (IR.item_pts_to (owner node) (item_record value link))
    as (IR.item_pts_to item (item_record value link));
}

ghost
fn value_close (node: X.lref) (item: item_ref) (#value: Int32.t)
               (#link: N.struct_list_node)
  requires IR.item_pts_to item (item_record value link) **
    pure (item == owner node /\ IR.item_embedded node)
  ensures item_ipl node value ** R.pts_to node link
{
  rewrite (IR.item_pts_to item (item_record value link))
    as (IR.item_pts_to (owner node) (item_record value link));
  IR.item_unfold (owner node) (item_record value link);
  rewrite (IR.item_link ((owner node)) link) as (R.pts_to node link);
  fold (item_ipl node value);
}

ghost
fn payload_to_item (node: X.lref) (#value: Int32.t) (#link: N.struct_list_node)
  requires item_ipl node value ** R.pts_to node link
  ensures IR.item_pts_to (owner node) (item_record value link)
{
  unfold (item_ipl node value);
  rewrite (R.pts_to node link)
    as (IR.item_link ((owner node)) link);
  IR.item_fold (owner node) value link;
}

ghost
fn item_to_payload (item: item_ref) (#v: I.struct_item)
  requires IR.item_pts_to item v
  ensures item_ipl (IR.item_link_1 item) v.I.fld_value **
    IR.item_link (item) v.I.fld_link
{
  IR.item_unfold item v;
  rewrite (IR.item_unfolded item 1.0R)
    as (IR.item_unfolded (owner (IR.item_link_1 item)) 1.0R);
  rewrite (IR.item_value (item) v.I.fld_value)
    as (IR.item_value ((owner (IR.item_link_1 item))) v.I.fld_value);
  fold (item_ipl (IR.item_link_1 item) v.I.fld_value);
}

ghost
(* Local structs already carry whole-item ownership in Palow. *)
fn fold_item (item: item_ref) (#v: I.struct_item)
  preserves IR.item_pts_to item v
{
  ()
}

ghost
(* The caller still owns the item whole -- it was handed one, and has not
   given any of it away -- so what has to be split off here is the link. *)
fn prepare_item (item: item_ref) (node: X.lref)
                (#value: Int32.t) (#link: N.struct_list_node)
  requires IR.item_pts_to item (item_record value link) **
    pure (node == IR.item_link_1 item)
  ensures item_ipl node value ** R.pts_to_uninit node
{
  IR.item_unfold item (item_record value link);
  rewrite (IR.item_unfolded item 1.0R)
    as (IR.item_unfolded (owner node) 1.0R);
  rewrite (IR.item_value (item) value)
    as (IR.item_value ((owner node)) value);
  fold (item_ipl node value);
  rewrite (IR.item_link (item) link) as (R.pts_to node link);
  R.forget node;
}

let first_match (key: Int32.t) (es: entries) : GTot item_ref =
  match X.first_match_entry (matches_value key) es with
  | None -> R.null
  | Some e -> owner (fst e)

let pop_post (head: X.lref) (es: entries) (result: item_ref) : slprop =
  match es with
  | [] -> X.is_list_ring_ix item_ipl head 1.0R [] ** pure (result == R.null)
  | e :: rest ->
    X.is_list_ring_ix item_ipl head 1.0R rest **
    (exists* (link: N.struct_list_node).
      IR.item_pts_to (owner (fst e)) (item_record (snd e) link)) **
    pure (result == owner (fst e))

ghost
fn close_pop_empty (head: X.lref) (es: entries)
  requires Q.pop_post item_ipl head es R.null ** pure (es == [])
  ensures pop_post head es R.null
{
  rewrite (Q.pop_post item_ipl head es R.null) as (Q.pop_post item_ipl head [] R.null);
  unfold (Q.pop_post item_ipl head [] R.null);
  fold (pop_post head [] R.null);
  rewrite (pop_post head [] R.null) as (pop_post head es R.null);
}

ghost
fn close_pop (head node: X.lref) (es: entries)
  requires Q.pop_post item_ipl head es node ** pure (Cons? es)
  ensures pop_post head es (owner node)
{
  match es {
    Nil -> { unreachable (); }
    Cons e rest -> {
      unfold (Q.pop_post item_ipl head es node);
      with link. assert (R.pts_to (fst e) link);
      payload_to_item (fst e);
      fold (pop_post head es (owner node));
    }
  }
}

let rec detached (es: entries) : Tot slprop (decreases es) =
  match es with
  | [] -> emp
  | e :: rest ->
    (exists* (link: N.struct_list_node).
      IR.item_pts_to (owner (fst e)) (item_record (snd e) link)) **
    detached rest

ghost
fn rec close_detached (es: entries)
  requires X.detached item_ipl es
  ensures detached es
  decreases es
{
  match es {
    Nil -> {
      unfold (X.detached item_ipl es);
      fold (detached es);
    }
    Cons e rest -> {
      unfold (X.detached item_ipl es);
      with link. assert (R.pts_to (fst e) link);
      payload_to_item (fst e);
      close_detached rest;
      fold (detached es);
    }
  }
}

ghost
fn pop_empty_result (head: X.lref) (result: item_ref)
  requires pop_post head [] result
  ensures X.is_list_ring_ix item_ipl head 1.0R [] ** pure (result == R.null)
{
  unfold (pop_post head [] result);
}

ghost
fn pop_one (head: X.lref) (item result: item_ref) (description: Int32.t)
           (rest: entries)
  requires pop_post head ((IR.item_link_1 item, description) :: rest) result
  ensures X.is_list_ring_ix item_ipl head 1.0R rest **
    (exists* (link: N.struct_list_node).
      IR.item_pts_to item (item_record description link)) **
    pure (result == item)
{
  unfold (pop_post head ((IR.item_link_1 item, description) :: rest) result);
  with link. assert (IR.item_pts_to (owner (IR.item_link_1 item))
    (item_record description link));
  rewrite (IR.item_pts_to (owner (IR.item_link_1 item)) (item_record description link))
    as (IR.item_pts_to item (item_record description link));
}
ghost
fn detached_one (item: item_ref) (description: Int32.t) (#es: entries)
  requires detached es ** pure (es == [(IR.item_link_1 item, description)])
  ensures exists* (link: N.struct_list_node).
    IR.item_pts_to item (item_record description link)
{
  rewrite (detached es) as (detached [(IR.item_link_1 item, description)]);
  unfold (detached [(IR.item_link_1 item, description)]);
  unfold (detached []);
  with link. assert (IR.item_pts_to (owner (IR.item_link_1 item))
    (item_record description link));
  rewrite (IR.item_pts_to (owner (IR.item_link_1 item)) (item_record description link))
    as (IR.item_pts_to item (item_record description link));
}
