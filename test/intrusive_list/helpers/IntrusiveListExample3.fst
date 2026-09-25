module IntrusiveListExample3

(* FIFO contracts track addresses, not per-entry descriptions. Queued ownership
   fixes ready=true; dequeue restores a whole item whose flag has been cleared. *)

open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module U = IntrusiveList
module R = IntrusiveListNodeRef
module IR = IntrusiveListItemRefs
module N = Struct_list_node
module I = Struct_item3

unfold let item_ref = R.ref I.struct_item3
(* The item points-to under whatever name the memory model gives it, so that
   one set of C annotations serves both models. *)
unfold let item_pts_to (r: item_ref) (v: I.struct_item3) : slprop = IR.item3_pts_to r v

(* The link field's address, under whatever name the memory model gives it. *)
unfold let item_link (r: item_ref) : U.lref = IR.item3_link_1 r


unfold let owner (node: U.lref) : item_ref = IR.item3_container node

(* A queued item owns a true flag, not an existentially chosen flag value. *)
let ready_payload (node: U.lref) : slprop =
  IR.item3_unfolded (owner node) 1.0R **
  IR.item3_ready ((owner node)) true **
  (* See `IntrusiveListItemRefs.item3_embedded`. *)
  pure (IR.item3_embedded node)

let payload : U.payload = U.of_unary ready_payload

unfold let item_record (ready: bool) (link: N.struct_list_node) =
  { I.fld_ready = ready; I.fld_link = link; }

ghost
(* Palow writes `item->ready` through the item's own points-to, so opening
   and closing the item for a field write have nothing left to do. The two
   remain because the C names them, and because under the current model they
   are real. *)
fn open_item (item: item_ref) (#v: I.struct_item3)
  preserves IR.item3_pts_to item v
{
  ()
}

ghost
fn fold_item (item: item_ref) (#v: I.struct_item3)
  preserves IR.item3_pts_to item v
{
  ()
}

ghost
fn prepare_enqueue (item: item_ref) (node: U.lref) (#link: N.struct_list_node)
  requires IR.item3_pts_to item (item_record true link) **
    pure (node == IR.item3_link_1 item)
  ensures payload node () ** R.pts_to_uninit node
{
  IR.item3_unfold item (item_record true link);
  rewrite (IR.item3_link (item) link) as (R.pts_to node link);
  rewrite (IR.item3_unfolded item 1.0R)
    as (IR.item3_unfolded (owner node) 1.0R);
  rewrite (IR.item3_ready (item) true)
    as (IR.item3_ready ((owner node)) true);
  fold (ready_payload node);
  rewrite (ready_payload node) as (payload node ());
  R.forget node;
}

ghost
fn enqueue_finish (head: U.lref) (item: item_ref) (node: U.lref) (nodes: list U.lref)
  requires U.is_list_ring_with payload head 1.0R (nodes @ [node]) **
    pure (node == IR.item3_link_1 item)
  ensures U.is_list_ring_with payload head 1.0R (nodes @ [IR.item3_link_1 item])
{
  rewrite (U.is_list_ring_with payload head 1.0R (nodes @ [node]))
    as (U.is_list_ring_with payload head 1.0R (nodes @ [IR.item3_link_1 item]));
}

let dequeue_post (head: U.lref) (nodes: list U.lref) (result: item_ref) : slprop =
  match nodes with
  | [] -> U.is_list_ring_with payload head 1.0R [] ** pure (result == R.null)
  | node :: rest ->
    U.is_list_ring_with payload head 1.0R rest **
    (exists* (link: N.struct_list_node). IR.item3_pts_to (owner node) (item_record false link)) **
    pure (result == owner node)

let pop_rest (head node: U.lref) (nodes: list U.lref) : slprop =
  match nodes with
  | [] -> pure False
  | first :: rest -> U.is_list_ring_with payload head 1.0R rest ** pure (node == first)

ghost
fn pop_empty (head: U.lref) (nodes: list U.lref)
  requires U.is_list_ring_with payload head 1.0R nodes ** pure (nodes == [])
  ensures dequeue_post head nodes R.null
{
  rewrite (U.is_list_ring_with payload head 1.0R nodes)
    as (U.is_list_ring_with payload head 1.0R []);
  fold (dequeue_post head [] R.null);
  rewrite (dequeue_post head [] R.null) as (dequeue_post head nodes R.null);
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
(* The payload owns the item apart from its link, and the list owns the link;
   Palow writes `item->ready` through the item as a whole, so opening the
   payload means joining the two back up. *)
fn ready_open (node: U.lref) (item: item_ref) (#link: N.struct_list_node)
  requires payload node () ** R.pts_to node link ** pure (item == owner node)
  ensures IR.item3_pts_to item (item_record true link) **
    (* Carried out so that closing the payload again can recover the item
       from its link; see `IntrusiveListItemRefs.item3_embedded`. *)
    pure (IR.item3_embedded node)
{
  rewrite (payload node ()) as (ready_payload node);
  unfold (ready_payload node);
  rewrite (R.pts_to node link) as (IR.item3_link ((owner node)) link);
  IR.item3_fold (owner node) true link;
  rewrite (IR.item3_pts_to (owner node) (item_record true link))
    as (IR.item3_pts_to item (item_record true link));
}

ghost
fn close_dequeue (head node: U.lref) (item: item_ref) (nodes: list U.lref)
                 (#link: N.struct_list_node)
  requires IR.item3_pts_to item (item_record false link) **
    pop_rest head node nodes **
    (* See `IntrusiveListItemRefs.item3_embedded`. *)
    pure (item == owner node /\ IR.item3_embedded node)
  ensures dequeue_post head nodes item
{
  match nodes {
    Nil -> { unfold (pop_rest head node nodes); unreachable (); }
    Cons first rest -> {
      unfold (pop_rest head node nodes);
      rewrite (IR.item3_pts_to item (item_record false link))
        as (IR.item3_pts_to (owner first) (item_record false link));
      fold (dequeue_post head nodes item);
    }
  }
}

ghost
fn pop_empty_result (head: U.lref) (result: item_ref)
  requires dequeue_post head [] result
  ensures U.is_list_ring_with payload head 1.0R [] ** pure (result == R.null)
{
  unfold (dequeue_post head [] result);
}

ghost
fn pop_one (head: U.lref) (expected result: item_ref) (rest: list U.lref)
  requires dequeue_post head (IR.item3_link_1 expected :: rest) result
  ensures U.is_list_ring_with payload head 1.0R rest **
    (exists* (link: N.struct_list_node). IR.item3_pts_to expected (item_record false link)) **
    pure (result == expected)
{
  unfold (dequeue_post head (IR.item3_link_1 expected :: rest) result);
  with link. assert (IR.item3_pts_to (owner (IR.item3_link_1 expected)) (item_record false link));
  rewrite (IR.item3_pts_to (owner (IR.item3_link_1 expected)) (item_record false link))
    as (IR.item3_pts_to expected (item_record false link));
}
