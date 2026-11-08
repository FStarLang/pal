module IntrusiveList

(* The nonindexed API specializes Indexed at unit and tracks node sequences.
   A unary payload can still specify field values and ownership. The F* operation
   wrappers check all nine generated C contracts; later adapters support client3. *)

open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module X = IntrusiveListIndexed
module C = IntrusiveListContext
module R = IntrusiveListNodeRef

unfold let lref = X.lref
unfold let payload = X.ipayload unit

(* The unindexed API is only the unit specialization of the indexed model. *)
let rec entries (nodes: list lref) : Tot (X.entries unit) (decreases nodes) =
  match nodes with
  | [] -> []
  | node :: rest -> (node, ()) :: entries rest

let of_unary (p: lref -> slprop) : payload = fun node () -> p node

let is_list_seg_with (p: payload) (prev cur endl: lref) (permission: perm)
                     (nodes: list lref) : slprop =
  X.is_list_seg_ix p prev cur endl permission (entries nodes)

let is_list_ring_with (p: payload) ([@@@mkey] head: lref) (permission: perm)
                      (nodes: list lref) : slprop =
  X.is_list_ring_ix p head permission (entries nodes)

let rec entries_append (front back: list lref)
  : Lemma (entries (front @ back) == entries front @ entries back)
    (decreases front) =
  match front with
  | [] -> ()
  | _ :: rest -> entries_append rest back

let rec entries_nodes (nodes: list lref)
  : Lemma (X.cells_of (entries nodes) == nodes) (decreases nodes) =
  match nodes with
  | [] -> ()
  | _ :: rest -> entries_nodes rest

let rec nodes_entries (es: X.entries unit)
  : Lemma (entries (X.cells_of es) == es) (decreases es) =
  match es with
  | [] -> ()
  | _ :: rest -> nodes_entries rest

ghost
fn ring_to_indexed (p: payload) (head: lref) (permission: perm) (nodes: list lref)
  requires is_list_ring_with p head permission nodes
  ensures X.is_list_ring_ix p head permission (entries nodes)
{
  unfold (is_list_ring_with p head permission nodes);
}

ghost
fn ring_from_indexed (p: payload) (head: lref) (permission: perm) (nodes: list lref)
  requires X.is_list_ring_ix p head permission (entries nodes)
  ensures is_list_ring_with p head permission nodes
{
  fold (is_list_ring_with p head permission nodes);
}

ghost
fn segment_to_indexed (p: payload) (prev cur endl: lref)
                     (permission: perm) (nodes: list lref)
  requires is_list_seg_with p prev cur endl permission nodes
  ensures X.is_list_seg_ix p prev cur endl permission (entries nodes)
{
  unfold (is_list_seg_with p prev cur endl permission nodes);
}

ghost
fn segment_from_indexed (p: payload) (prev cur endl: lref)
                       (permission: perm) (nodes: list lref)
  requires X.is_list_seg_ix p prev cur endl permission (entries nodes)
  ensures is_list_seg_with p prev cur endl permission nodes
{
  fold (is_list_seg_with p prev cur endl permission nodes);
}

unfold let model (p: payload) (nodes: list lref) : C.context =
  C.make p (entries nodes)

unfold let insertion (p: payload) (nodes: list lref) : C.insertion = {
  C.model = model p nodes;
  C.description = ();
}

unfold let cut (p: payload) (head: lref) (front back: list lref)
               (nodes: list lref) : C.cut = {
  C.model = model p nodes;
  C.head = head;
  C.front = entries front;
  C.back = entries back;
  C.description = ();
}

(* The unit wrappers use the indexed C contracts, not another surgery proof. *)
divergent fn init (#p: erased payload) (head: lref)
  requires R.pts_to_uninit head
  ensures is_list_ring_with (reveal p) head 1.0R []
{
  C.prepare_init (model (reveal p) []) head;
  Func_list_init.func_list_init head;
  C.finish_ring (model (reveal p) []) head;
  ring_from_indexed (reveal p) head 1.0R [];
}

divergent fn empty (#p: erased payload) (#nodes: erased (list lref)) (head: lref)
  requires is_list_ring_with (reveal p) head 1.0R (reveal nodes)
  returns result: bool
  ensures is_list_ring_with (reveal p) head 1.0R (reveal nodes) **
    pure (result <==> reveal nodes == [])
{
  ring_to_indexed (reveal p) head 1.0R (reveal nodes);
  C.prepare_ring (model (reveal p) (reveal nodes)) head;
  let result = Func_list_empty.func_list_empty head;
  unfold (C.empty_post (model (reveal p) (reveal nodes)) head result);
  C.finish_ring (model (reveal p) (reveal nodes)) head;
  entries_nodes (reveal nodes);
  ring_from_indexed (reveal p) head 1.0R (reveal nodes);
  return result;
}

divergent fn validate (#p: erased payload) (#front #back: erased (list lref))
                      (head node: lref)
  requires is_list_ring_with (reveal p) head 1.0R (reveal front @ reveal back) **
    pure (node == X.last_or head (entries (reveal front)))
  ensures is_list_ring_with (reveal p) head 1.0R (reveal front @ reveal back)
{
  entries_append (reveal front) (reveal back);
  ring_to_indexed (reveal p) head 1.0R (reveal front @ reveal back);
  C.prepare_validation (reveal p) head node
    (entries (reveal front)) (entries (reveal back));
  Func_list_validate.func_list_validate node;
  C.finish_validation (reveal p) head node
    (entries (reveal front)) (entries (reveal back));
  ring_from_indexed (reveal p) head 1.0R (reveal front @ reveal back);
}

divergent fn insert_head (#p: erased payload) (#nodes: erased (list lref))
                         (head entry: lref)
  requires is_list_ring_with (reveal p) head 1.0R (reveal nodes) **
    R.pts_to_uninit entry ** (reveal p) entry ()
  ensures is_list_ring_with (reveal p) head 1.0R (entry :: reveal nodes)
{
  ring_to_indexed (reveal p) head 1.0R (reveal nodes);
  C.prepare_ring (model (reveal p) (reveal nodes)) head;
  fold (C.insert_pre (insertion (reveal p) (reveal nodes)) head entry);
  Func_list_insert_head.func_list_insert_head head entry;
  unfold (C.insert_head_post (insertion (reveal p) (reveal nodes)) head entry);
  ring_from_indexed (reveal p) head 1.0R (entry :: reveal nodes);
}

divergent fn insert_tail (#p: erased payload) (#nodes: erased (list lref))
                         (head entry: lref)
  requires is_list_ring_with (reveal p) head 1.0R (reveal nodes) **
    R.pts_to_uninit entry ** (reveal p) entry ()
  ensures is_list_ring_with (reveal p) head 1.0R (reveal nodes @ [entry])
{
  ring_to_indexed (reveal p) head 1.0R (reveal nodes);
  C.prepare_ring (model (reveal p) (reveal nodes)) head;
  fold (C.insert_pre (insertion (reveal p) (reveal nodes)) head entry);
  Func_list_insert_tail.func_list_insert_tail head entry;
  unfold (C.insert_tail_post (insertion (reveal p) (reveal nodes)) head entry);
  entries_append (reveal nodes) [entry];
  ring_from_indexed (reveal p) head 1.0R (reveal nodes @ [entry]);
}

divergent fn insert_after (#p: erased payload) (#front #back: erased (list lref))
                          (head position entry: lref)
  requires is_list_ring_with (reveal p) head 1.0R (reveal front @ reveal back) **
    pure (position == X.last_or head (entries (reveal front))) **
    R.pts_to_uninit entry ** (reveal p) entry ()
  ensures is_list_ring_with (reveal p) head 1.0R (reveal front @ (entry :: reveal back))
{
  entries_append (reveal front) (reveal back);
  ring_to_indexed (reveal p) head 1.0R (reveal front @ reveal back);
  C.prepare_ring (model (reveal p) (reveal front @ reveal back)) head;
  fold (C.insert_after_pre
    (cut (reveal p) head (reveal front) (reveal back) (reveal front @ reveal back))
    position entry);
  Func_list_insert_after.func_list_insert_after position entry;
  unfold (C.insert_after_post
    (cut (reveal p) head (reveal front) (reveal back) (reveal front @ reveal back)) entry);
  entries_append (reveal front) (entry :: reveal back);
  ring_from_indexed (reveal p) head 1.0R (reveal front @ (entry :: reveal back));
}

divergent fn remove (#p: erased payload) (#front #back: erased (list lref))
                    (head entry: lref)
  requires is_list_ring_with (reveal p) head 1.0R (reveal front @ (entry :: reveal back))
  returns result: bool
  ensures is_list_ring_with (reveal p) head 1.0R (reveal front @ reveal back) **
    R.pts_to entry (X.mklink
      (X.first_or head (entries (reveal back)))
      (X.last_or head (entries (reveal front)))) **
    (reveal p) entry () ** pure (result <==> reveal front @ reveal back == [])
{
  entries_append (reveal front) (entry :: reveal back);
  ring_to_indexed (reveal p) head 1.0R (reveal front @ (entry :: reveal back));
  C.prepare_ring (model (reveal p) (reveal front @ (entry :: reveal back))) head;
  fold (C.remove_pre
    (cut (reveal p) head (reveal front) (reveal back)
      (reveal front @ (entry :: reveal back))) entry);
  let result = Func_list_remove.func_list_remove entry;
  unfold (C.remove_post
    (cut (reveal p) head (reveal front) (reveal back)
      (reveal front @ (entry :: reveal back))) entry result);
  entries_append (reveal front) (reveal back);
  entries_nodes (reveal front @ reveal back);
  ring_from_indexed (reveal p) head 1.0R (reveal front @ reveal back);
  return result;
}

divergent fn remove_head (#p: erased payload) (#rest: erased (list lref))
                         (head node: lref)
  requires is_list_ring_with (reveal p) head 1.0R (node :: reveal rest)
  returns result: lref
  ensures is_list_ring_with (reveal p) head 1.0R (reveal rest) **
    (exists* (next: lref). R.pts_to result (X.mklink next head)) **
    (reveal p) result () ** pure (result == node)
{
  ring_to_indexed (reveal p) head 1.0R (node :: reveal rest);
  C.prepare_ring (model (reveal p) (node :: reveal rest)) head;
  fold (C.remove_head_pre (model (reveal p) (node :: reveal rest)) head);
  let result = Func_list_remove_head.func_list_remove_head head;
  rewrite (C.remove_head_post (model (reveal p) (node :: reveal rest)) head result)
    as (C.remove_head_post
      (C.make (reveal p) ((node, ()) :: entries (reveal rest))) head result);
  unfold (C.remove_head_post
    (C.make (reveal p) ((node, ()) :: entries (reveal rest))) head result);
  ring_from_indexed (reveal p) head 1.0R (reveal rest);
  return result;
}

divergent fn move (#p: erased payload)
                  (#source_nodes #destination_nodes: erased (list lref))
                  (source destination: lref)
  requires is_list_ring_with (reveal p) source 1.0R (reveal source_nodes) **
    is_list_ring_with (reveal p) destination 1.0R (reveal destination_nodes)
  ensures is_list_ring_with (reveal p) source 1.0R [] **
    is_list_ring_with (reveal p) destination 1.0R
      (reveal destination_nodes @ reveal source_nodes)
{
  ring_to_indexed (reveal p) source 1.0R (reveal source_nodes);
  ring_to_indexed (reveal p) destination 1.0R (reveal destination_nodes);
  C.prepare_move (reveal p) source destination
    (entries (reveal source_nodes)) (entries (reveal destination_nodes));
  Func_list_move.func_list_move source destination;
  C.finish_move (reveal p) source destination
    (entries (reveal source_nodes)) (entries (reveal destination_nodes));
  entries_append (reveal destination_nodes) (reveal source_nodes);
  ring_from_indexed (reveal p) source 1.0R [];
  ring_from_indexed (reveal p) destination 1.0R
    (reveal destination_nodes @ reveal source_nodes);
}

(* Proof-only selection of the payload for initialization through C. *)
let init_pre (p: payload) (head: lref) : slprop = R.pts_to_uninit head

ghost
fn prepare_init (p: payload) (head: lref)
  requires R.pts_to_uninit head
  ensures init_pre p head
{
  fold (init_pre p head);
}

ghost
fn init_open (p: payload) (head: lref)
  requires init_pre p head
  ensures C.init_pre (model p []) head
{
  unfold (init_pre p head);
  C.prepare_init (model p []) head;
}

ghost
fn init_close (p: payload) (head: lref)
  requires C.ring (model p []) head
  ensures is_list_ring_with p head 1.0R []
{
  C.finish_ring (model p []) head;
  ring_from_indexed p head 1.0R [];
}

ghost
fn empty_open (p: payload) (head: lref) (nodes: list lref)
  requires is_list_ring_with p head 1.0R nodes
  ensures C.ring (model p nodes) head
{
  ring_to_indexed p head 1.0R nodes;
  C.prepare_ring (model p nodes) head;
}

ghost
fn empty_close (p: payload) (head: lref) (nodes: list lref) (#result: bool)
  requires C.empty_post (model p nodes) head result
  ensures is_list_ring_with p head 1.0R nodes ** pure (result <==> nodes == [])
{
  unfold (C.empty_post (model p nodes) head result);
  C.finish_ring (model p nodes) head;
  entries_nodes nodes;
  ring_from_indexed p head 1.0R nodes;
}

ghost
fn validate_head_open (p: payload) (head: lref) (nodes: list lref)
  requires is_list_ring_with p head 1.0R nodes
  ensures C.validation_pre (C.validation_of p head [] (entries nodes)) head
{
  ring_to_indexed p head 1.0R nodes;
  C.prepare_validation p head head [] (entries nodes);
}

ghost
fn validate_head_close (p: payload) (head: lref) (nodes: list lref)
  requires C.validation_pre (C.validation_of p head [] (entries nodes)) head
  ensures is_list_ring_with p head 1.0R nodes
{
  C.finish_validation p head head [] (entries nodes);
  ring_from_indexed p head 1.0R nodes;
}

let tail_pre (p: payload) (head entry: lref) (nodes: list lref) : slprop =
  is_list_ring_with p head 1.0R nodes ** R.pts_to_uninit entry ** p entry ()

ghost
fn prepare_tail (p: payload) (head entry: lref) (nodes: list lref)
  requires is_list_ring_with p head 1.0R nodes ** R.pts_to_uninit entry ** p entry ()
  ensures tail_pre p head entry nodes
{
  fold (tail_pre p head entry nodes);
}

ghost
fn tail_open (p: payload) (head entry: lref) (nodes: list lref)
  requires tail_pre p head entry nodes
  ensures C.insert_pre (insertion p nodes) head entry
{
  unfold (tail_pre p head entry nodes);
  ring_to_indexed p head 1.0R nodes;
  C.prepare_ring (model p nodes) head;
  fold (C.insert_pre (insertion p nodes) head entry);
}

ghost
fn tail_close (p: payload) (head entry: lref) (nodes: list lref)
  requires C.insert_tail_post (insertion p nodes) head entry
  ensures is_list_ring_with p head 1.0R (nodes @ [entry])
{
  unfold (C.insert_tail_post (insertion p nodes) head entry);
  entries_append nodes [entry];
  ring_from_indexed p head 1.0R (nodes @ [entry]);
}

let pop_post (p: payload) (head: lref) (nodes: list lref) (result: lref) : slprop =
  match nodes with
  | [] -> pure False
  | node :: rest ->
    is_list_ring_with p head 1.0R rest **
    (exists* (next: lref). R.pts_to result (X.mklink next head)) **
    p result () ** pure (result == node)

ghost
fn pop_open (p: payload) (head: lref) (nodes: list lref)
  requires is_list_ring_with p head 1.0R nodes ** pure (nodes =!= [])
  ensures C.remove_head_pre (model p nodes) head
{
  ring_to_indexed p head 1.0R nodes;
  entries_nodes nodes;
  C.prepare_pop p head (entries nodes);
}

ghost
fn pop_close (p: payload) (head result: lref) (nodes: list lref)
  requires C.remove_head_post (model p nodes) head result ** pure (nodes =!= [])
  ensures pop_post p head nodes result
{
  match nodes {
    Nil -> { unreachable (); }
    Cons node rest -> {
      rewrite (C.remove_head_post (model p nodes) head result)
        as (C.remove_head_post (C.make p ((node, ()) :: entries rest)) head result);
      unfold (C.remove_head_post (C.make p ((node, ()) :: entries rest)) head result);
      ring_from_indexed p head 1.0R rest;
      fold (pop_post p head nodes result);
    }
  }
}

ghost
fn move_open (p: payload) (source destination: lref)
             (source_nodes destination_nodes: list lref)
  requires is_list_ring_with p source 1.0R source_nodes **
    is_list_ring_with p destination 1.0R destination_nodes
  ensures C.move_pre (C.movement_of p (entries source_nodes) (entries destination_nodes))
    source destination
{
  ring_to_indexed p source 1.0R source_nodes;
  ring_to_indexed p destination 1.0R destination_nodes;
  C.prepare_move p source destination (entries source_nodes) (entries destination_nodes);
}

ghost
fn move_close (p: payload) (source destination: lref)
              (source_nodes destination_nodes: list lref)
  requires C.move_post (C.movement_of p (entries source_nodes) (entries destination_nodes))
    source destination
  ensures is_list_ring_with p source 1.0R [] **
    is_list_ring_with p destination 1.0R (destination_nodes @ source_nodes)
{
  C.finish_move p source destination (entries source_nodes) (entries destination_nodes);
  entries_append destination_nodes source_nodes;
  ring_from_indexed p source 1.0R [];
  ring_from_indexed p destination 1.0R (destination_nodes @ source_nodes);
}

ghost
(* See `IntrusiveListOps.indexed_release_empty`. *)
fn release_empty (p: payload) (head: lref)
  requires is_list_ring_with p head 1.0R []
  ensures R.pts_to_uninit head
{
  ring_to_indexed p head 1.0R [];
  X.ring_elim_empty p head;
  R.forget head;
}
