module IntrusiveListExample

(* Integer-item adapters for client.c. The final checks also exercise uninhabited
   descriptions, emp payloads, and separately owned list-valued descriptions. *)

open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module R = Pulse.Lib.Reference
module N = Struct_list_node
module I = Struct_item
module Q = IntrusiveListItems
module X = IntrusiveListIndexed
module C = IntrusiveListContext

(* Concrete payload ownership belongs here; reusable list helpers do not import this module. *)
unfold let entries = X.entries Int32.t
unfold let item_ref = ref I.struct_item

unfold let owner (node: X.lref) : item_ref =
  I.struct_item__link_container node

let item_ipl : X.ipayload Int32.t =
  fun node value ->
    I.struct_item__aux_raw_unfolded (owner node) 1.0R **
    R.pts_to (I.struct_item__value_1 (owner node)) value

unfold let item_record (value: Int32.t) (link: N.struct_list_node) =
  { I.struct_item__value = value; I.struct_item__link = link; }

let matches_value (key: Int32.t) (_node: X.lref) (value: Int32.t) : GTot bool =
  value == key

let value_le (x y: Int32.t) : GTot bool =
  Int32.v x <= Int32.v y

let value_order () : Lemma (X.total_preorder value_le) = ()

ghost
fn value_open (node: X.lref) (item: item_ref) (#value: Int32.t)
  requires item_ipl node value ** pure (item == owner node)
  ensures I.struct_item__aux_raw_unfolded item 1.0R **
    R.pts_to (I.struct_item__value_1 item) value
{
  unfold (item_ipl node value);
  rewrite (I.struct_item__aux_raw_unfolded (owner node) 1.0R)
    as (I.struct_item__aux_raw_unfolded item 1.0R);
  rewrite (R.pts_to (I.struct_item__value_1 (owner node)) value)
    as (R.pts_to (I.struct_item__value_1 item) value);
}

ghost
fn value_close (node: X.lref) (item: item_ref) (#value: Int32.t)
  requires I.struct_item__aux_raw_unfolded item 1.0R **
    R.pts_to (I.struct_item__value_1 item) value **
    pure (item == owner node)
  ensures item_ipl node value
{
  rewrite (I.struct_item__aux_raw_unfolded item 1.0R)
    as (I.struct_item__aux_raw_unfolded (owner node) 1.0R);
  rewrite (R.pts_to (I.struct_item__value_1 item) value)
    as (R.pts_to (I.struct_item__value_1 (owner node)) value);
  fold (item_ipl node value);
}

ghost
fn payload_to_item (node: X.lref) (#value: Int32.t) (#link: N.struct_list_node)
  requires item_ipl node value ** R.pts_to node link
  ensures R.pts_to (owner node) (item_record value link)
{
  unfold (item_ipl node value);
  rewrite (R.pts_to node link)
    as (R.pts_to (I.struct_item__link_1 (owner node)) link);
  I.struct_item__aux_raw_fold (owner node) value link;
}

ghost
fn item_to_payload (item: item_ref) (#v: I.struct_item)
  requires R.pts_to item v
  ensures item_ipl (I.struct_item__link_1 item) v.I.struct_item__value **
    R.pts_to (I.struct_item__link_1 item) v.I.struct_item__link
{
  I.struct_item__aux_raw_unfold item v;
  value_close (I.struct_item__link_1 item) item;
}

ghost
fn fold_item (item: item_ref) (#value: Int32.t) (#link: N.struct_list_node)
  requires I.struct_item__aux_raw_unfolded item 1.0R **
    R.pts_to (I.struct_item__value_1 item) value **
    R.pts_to (I.struct_item__link_1 item) link
  ensures R.pts_to item (item_record value link)
{
  I.struct_item__aux_raw_fold item value link;
}

ghost
fn prepare_item (item: item_ref) (node: X.lref)
                (#value: Int32.t) (#link: N.struct_list_node)
  requires I.struct_item__aux_raw_unfolded item 1.0R **
    R.pts_to (I.struct_item__value_1 item) value ** R.pts_to node link **
    pure (node == I.struct_item__link_1 item)
  ensures item_ipl node value ** R.pts_to_uninit node
{
  value_close node item;
  Pulse.Lib.C.MaybeUninit.intro_maybe_some node;
  Pulse.Lib.C.MaybeUninit.forget_maybe node;
}

let first_match (key: Int32.t) (es: entries) : GTot item_ref =
  match X.first_match_entry (matches_value key) es with
  | None -> null
  | Some e -> owner (fst e)

let pop_post (head: X.lref) (es: entries) (result: item_ref) : slprop =
  match es with
  | [] -> X.is_list_ring_ix item_ipl head 1.0R [] ** pure (result == null)
  | e :: rest ->
    X.is_list_ring_ix item_ipl head 1.0R rest **
    (exists* (link: N.struct_list_node).
      R.pts_to (owner (fst e)) (item_record (snd e) link)) **
    pure (result == owner (fst e))

ghost
fn close_pop_empty (head: X.lref) (es: entries)
  requires Q.pop_post item_ipl head es null ** pure (es == [])
  ensures pop_post head es null
{
  rewrite (Q.pop_post item_ipl head es null) as (Q.pop_post item_ipl head [] null);
  unfold (Q.pop_post item_ipl head [] null);
  fold (pop_post head [] null);
  rewrite (pop_post head [] null) as (pop_post head es null);
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
      R.pts_to (owner (fst e)) (item_record (snd e) link)) **
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
  ensures X.is_list_ring_ix item_ipl head 1.0R [] ** pure (result == null)
{
  unfold (pop_post head [] result);
}

ghost
fn pop_one (head: X.lref) (item result: item_ref) (description: Int32.t)
           (rest: entries)
  requires pop_post head ((I.struct_item__link_1 item, description) :: rest) result
  ensures X.is_list_ring_ix item_ipl head 1.0R rest **
    (exists* (link: N.struct_list_node).
      R.pts_to item (item_record description link)) **
    pure (result == item)
{
  unfold (pop_post head ((I.struct_item__link_1 item, description) :: rest) result);
  with link. assert (R.pts_to (owner (I.struct_item__link_1 item))
    (item_record description link));
  rewrite (R.pts_to (owner (I.struct_item__link_1 item)) (item_record description link))
    as (R.pts_to item (item_record description link));
}

ghost
fn detached_one (item: item_ref) (description: Int32.t) (#es: entries)
  requires detached es ** pure (es == [(I.struct_item__link_1 item, description)])
  ensures exists* (link: N.struct_list_node).
    R.pts_to item (item_record description link)
{
  rewrite (detached es) as (detached [(I.struct_item__link_1 item, description)]);
  unfold (detached [(I.struct_item__link_1 item, description)]);
  unfold (detached []);
  with link. assert (R.pts_to (owner (I.struct_item__link_1 item))
    (item_record description link));
  rewrite (R.pts_to (owner (I.struct_item__link_1 item)) (item_record description link))
    as (R.pts_to item (item_record description link));
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

let list_ipl (storage: X.lref -> ref (list Int32.t)) : X.ipayload (list Int32.t) =
  fun node description -> R.pts_to (storage node) description

let always_list : X.matcher (list Int32.t) = fun _ _ -> true
let never_list : X.matcher (list Int32.t) = fun _ _ -> false

ghost
fn check_list_payload_queries (storage: X.lref -> ref (list Int32.t))
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
fn check_list_payload_pop (storage: X.lref -> ref (list Int32.t))
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
