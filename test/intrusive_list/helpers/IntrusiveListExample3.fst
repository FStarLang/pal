module IntrusiveListExample3
open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module U = IntrusiveList
module R = Pulse.Lib.Reference
module N = Struct_list_node
module I = Struct_item3

unfold let item_ref = ref I.struct_item3
unfold let owner (node: U.lref) : item_ref = I.struct_item3__link_container node

(* A queued item owns a true flag, not an existentially chosen flag value. *)
let ready_payload (node: U.lref) : slprop =
  I.struct_item3__aux_raw_unfolded (owner node) 1.0R **
  R.pts_to (I.struct_item3__ready_1 (owner node)) true

let payload : U.payload = U.of_unary ready_payload

unfold let item_record (ready: bool) (link: N.struct_list_node) =
  { I.struct_item3__ready = ready; I.struct_item3__link = link; }

ghost
fn open_item (item: item_ref) (#v: I.struct_item3)
  requires R.pts_to item v
  ensures I.struct_item3__aux_raw_unfolded item 1.0R **
    R.pts_to (I.struct_item3__ready_1 item) v.I.struct_item3__ready **
    R.pts_to (I.struct_item3__link_1 item) v.I.struct_item3__link
{
  I.struct_item3__aux_raw_unfold item v;
}

ghost
fn fold_item (item: item_ref) (#ready: bool) (#link: N.struct_list_node)
  requires I.struct_item3__aux_raw_unfolded item 1.0R **
    R.pts_to (I.struct_item3__ready_1 item) ready **
    R.pts_to (I.struct_item3__link_1 item) link
  ensures R.pts_to item (item_record ready link)
{
  I.struct_item3__aux_raw_fold item ready link;
}

ghost
fn prepare_enqueue (item: item_ref) (node: U.lref) (#link: N.struct_list_node)
  requires I.struct_item3__aux_raw_unfolded item 1.0R **
    R.pts_to (I.struct_item3__ready_1 item) true ** R.pts_to node link **
    pure (node == I.struct_item3__link_1 item)
  ensures payload node () ** R.pts_to_uninit node
{
  rewrite (I.struct_item3__aux_raw_unfolded item 1.0R)
    as (I.struct_item3__aux_raw_unfolded (owner node) 1.0R);
  rewrite (R.pts_to (I.struct_item3__ready_1 item) true)
    as (R.pts_to (I.struct_item3__ready_1 (owner node)) true);
  fold (ready_payload node);
  rewrite (ready_payload node) as (payload node ());
  Pulse.Lib.C.MaybeUninit.intro_maybe_some node;
  Pulse.Lib.C.MaybeUninit.forget_maybe node;
}

ghost
fn enqueue_finish (head: U.lref) (item: item_ref) (node: U.lref) (nodes: list U.lref)
  requires U.is_list_ring_with payload head 1.0R (nodes @ [node]) **
    pure (node == I.struct_item3__link_1 item)
  ensures U.is_list_ring_with payload head 1.0R (nodes @ [I.struct_item3__link_1 item])
{
  rewrite (U.is_list_ring_with payload head 1.0R (nodes @ [node]))
    as (U.is_list_ring_with payload head 1.0R (nodes @ [I.struct_item3__link_1 item]));
}

let dequeue_post (head: U.lref) (nodes: list U.lref) (result: item_ref) : slprop =
  match nodes with
  | [] -> U.is_list_ring_with payload head 1.0R [] ** pure (result == null)
  | node :: rest ->
    U.is_list_ring_with payload head 1.0R rest **
    (exists* (link: N.struct_list_node). R.pts_to (owner node) (item_record false link)) **
    pure (result == owner node)

let pop_rest (head node: U.lref) (nodes: list U.lref) : slprop =
  match nodes with
  | [] -> pure False
  | first :: rest -> U.is_list_ring_with payload head 1.0R rest ** pure (node == first)

ghost
fn pop_empty (head: U.lref) (nodes: list U.lref)
  requires U.is_list_ring_with payload head 1.0R nodes ** pure (nodes == [])
  ensures dequeue_post head nodes null
{
  rewrite (U.is_list_ring_with payload head 1.0R nodes)
    as (U.is_list_ring_with payload head 1.0R []);
  fold (dequeue_post head [] null);
  rewrite (dequeue_post head [] null) as (dequeue_post head nodes null);
}

ghost
fn pop_open (head node: U.lref) (nodes: list U.lref)
  requires U.pop_post payload head nodes node ** pure (nodes =!= [])
  ensures exists* (link: N.struct_list_node).
    R.pts_to node link ** payload node () ** pop_rest head node nodes
{
  match nodes {
    Nil -> { unreachable (); }
    Cons first rest -> {
      unfold (U.pop_post payload head nodes node);
      fold (pop_rest head node nodes);
    }
  }
}

ghost
fn ready_open (node: U.lref) (item: item_ref)
  requires payload node () ** pure (item == owner node)
  ensures I.struct_item3__aux_raw_unfolded item 1.0R **
    R.pts_to (I.struct_item3__ready_1 item) true
{
  rewrite (payload node ()) as (ready_payload node);
  unfold (ready_payload node);
  rewrite (I.struct_item3__aux_raw_unfolded (owner node) 1.0R)
    as (I.struct_item3__aux_raw_unfolded item 1.0R);
  rewrite (R.pts_to (I.struct_item3__ready_1 (owner node)) true)
    as (R.pts_to (I.struct_item3__ready_1 item) true);
}

ghost
fn close_dequeue (head node: U.lref) (item: item_ref) (nodes: list U.lref)
                 (#link: N.struct_list_node)
  requires I.struct_item3__aux_raw_unfolded item 1.0R **
    R.pts_to (I.struct_item3__ready_1 item) false ** R.pts_to node link **
    pop_rest head node nodes ** pure (item == owner node)
  ensures dequeue_post head nodes item
{
  match nodes {
    Nil -> { unfold (pop_rest head node nodes); unreachable (); }
    Cons first rest -> {
      unfold (pop_rest head node nodes);
      rewrite (R.pts_to node link) as (R.pts_to (I.struct_item3__link_1 item) link);
      fold_item item;
      rewrite (R.pts_to item (item_record false link))
        as (R.pts_to (owner first) (item_record false link));
      fold (dequeue_post head nodes item);
    }
  }
}

ghost
fn pop_empty_result (head: U.lref) (result: item_ref)
  requires dequeue_post head [] result
  ensures U.is_list_ring_with payload head 1.0R [] ** pure (result == null)
{
  unfold (dequeue_post head [] result);
}

ghost
fn pop_one (head: U.lref) (expected result: item_ref) (rest: list U.lref)
  requires dequeue_post head (I.struct_item3__link_1 expected :: rest) result
  ensures U.is_list_ring_with payload head 1.0R rest **
    (exists* (link: N.struct_list_node). R.pts_to expected (item_record false link)) **
    pure (result == expected)
{
  unfold (dequeue_post head (I.struct_item3__link_1 expected :: rest) result);
  with link. assert (R.pts_to (owner (I.struct_item3__link_1 expected)) (item_record false link));
  rewrite (R.pts_to (owner (I.struct_item3__link_1 expected)) (item_record false link))
    as (R.pts_to expected (item_record false link));
}
