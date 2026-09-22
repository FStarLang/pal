module IntrusiveListExample

(* Integer-item adapters for client.c. The final checks also exercise uninhabited
   descriptions, emp payloads, and separately owned list-valued descriptions. *)

open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module R = IntrusiveListNodeRef
module PR = Pulse.Lib.Reference
module IR = IntrusiveListItemRefs
module N = Struct_list_node
module I = Struct_item
module Q = IntrusiveListItems
module X = IntrusiveListIndexed
module C = IntrusiveListContext

(* Concrete payload ownership belongs here; reusable list helpers do not import this module. *)
unfold let entries = X.entries Int32.t
unfold let item_ref = R.ref I.struct_item
(* The item points-to under whatever name the memory model gives it, so that
   one set of C annotations serves both models. *)
unfold let item_pts_to (r: item_ref) (v: I.struct_item) : slprop = IR.item_pts_to r v

(* The link field's address, under whatever name the memory model gives it. *)
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
       from its link; see `IntrusiveListItemRefs.item_embedded`. *)
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
(* Palow initialises a local struct through its own points-to, so there is
   nothing left to fold. The name stays because the C names it, and because
   under the current model it is a real step. *)
fn fold_item (item: item_ref) (#v: I.struct_item)
  preserves IR.item_pts_to item v
{
  ()
}

ghost
fn prepare_item (item: item_ref) (node: X.lref)
                (#value: Int32.t) (#link: N.struct_list_node)
  requires IR.item_unfolded item 1.0R **
    IR.item_value (item) value ** R.pts_to node link **
    pure (node == IR.item_link_1 item)
  ensures item_ipl node value ** R.pts_to_uninit node
{
  rewrite (IR.item_unfolded item 1.0R)
    as (IR.item_unfolded (owner node) 1.0R);
  rewrite (IR.item_value (item) value)
    as (IR.item_value ((owner node)) value);
  fold (item_ipl node value);
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

(* These instantiations exercise descriptors without item fields or defaults. *)
type empty_description = u:unit{False}

let empty_ipl : X.ipayload empty_description = fun _ _ -> emp
let never_empty : X.matcher empty_description = fun _ _ -> false

ghost
fn check_empty_descriptions (head: X.lref)
  requires X.is_list_ring_ix empty_ipl head 1.0R []
  ensures X.is_list_ring_ix empty_ipl head 1.0R []
{
  X.head_open empty_ipl head [];
  Q.find_start empty_ipl never_empty head head [];
  Q.find_end empty_ipl never_empty head head [];
}

let unit_ipl : X.ipayload unit = fun _ _ -> emp
let always_unit : X.matcher unit = fun _ _ -> true

ghost
fn check_payload_free_query (head node: X.lref)
  requires X.is_list_ring_ix unit_ipl head 1.0R [(node, ())]
  ensures X.is_list_ring_ix unit_ipl head 1.0R [(node, ())]
{
  X.head_open unit_ipl head [(node, ())];
  Q.find_start unit_ipl always_unit head node [(node, ())];
  Q.find_open unit_ipl always_unit head node [(node, ())];
  with description. assert (unit_ipl node description);
  Q.find_found unit_ipl always_unit head node [(node, ())] description;
}

(* Deliberately not a C object: the point of this payload is that the list
   theory never looks at one, so an ordinary Pulse reference holding an
   ordinary list is the sharpest way to say so. *)
let list_ipl (storage: X.lref -> PR.ref (list Int32.t)) : X.ipayload (list Int32.t) =
  fun node description -> PR.pts_to (storage node) description

let always_list : X.matcher (list Int32.t) = fun _ _ -> true
let never_list : X.matcher (list Int32.t) = fun _ _ -> false

ghost
fn check_list_payload_queries (storage: X.lref -> PR.ref (list Int32.t))
                              (head node: X.lref) (description: list Int32.t)
  requires X.is_list_ring_ix (list_ipl storage) head 1.0R [(node, description)]
  ensures X.is_list_ring_ix (list_ipl storage) head 1.0R [(node, description)]
{
  X.head_open (list_ipl storage) head [(node, description)];
  Q.find_start (list_ipl storage) always_list head node [(node, description)];
  Q.find_open (list_ipl storage) always_list head node [(node, description)];
  with current. assert (list_ipl storage node current);
  Q.find_found (list_ipl storage) always_list head node [(node, description)] current;

  X.split_open (list_ipl storage) head [] [(node, description)];
  with pos. assert (X.split (list_ipl storage) head pos [] [(node, description)]);
  rewrite (X.split (list_ipl storage) head pos [] [(node, description)])
    as (X.split (list_ipl storage) head node [] [(node, description)]);
  X.cursor_expose (list_ipl storage) head node [] (node, description) [];
  with v. assert (R.pts_to node v);
  fold (Q.find_mid (list_ipl storage) never_list head node
    [(node, description)] description v);
  Q.find_step (list_ipl storage) never_list head node head
    [(node, description)] description;
  Q.find_end (list_ipl storage) never_list head head [(node, description)];
}

divergent
fn check_list_payload_pop (storage: X.lref -> PR.ref (list Int32.t))
                         (head node: X.lref) (description: list Int32.t)
  requires X.is_list_ring_ix (list_ipl storage) head 1.0R [(node, description)]
  ensures Q.pop_post (list_ipl storage) head [(node, description)] node
{
  C.prepare_pop (list_ipl storage) head [(node, description)];
  let result = Func_list_remove_head.func_list_remove_head head;
  Q.pop_finish (list_ipl storage) head result [(node, description)];
  unfold (Q.pop_post (list_ipl storage) head [(node, description)] result);
  fold (Q.pop_post (list_ipl storage) head [(node, description)] node);
}

let length_le (x y: list Int32.t) : GTot bool = length x <= length y

let length_order () : Lemma (X.total_preorder length_le) = ()

let check_stable_list_descriptions (first second: X.lref) (x y: list Int32.t)
  : Lemma
    (requires length x == length y)
    (ensures
      X.insert length_le second y [(first, x)] == [(first, x); (second, y)] /\
      X.sorted length_le (X.insert length_le second y [(first, x)]))
  =
  length_order ();
  X.insert_preserves_sorted length_le second y [(first, x)]
