module IntrusiveList
open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module B = IntrusiveListIndexed
module I = IntrusiveListIndexed
module C = IntrusiveListContext
module R = Pulse.Lib.Reference

unfold let lref = B.lref
unfold let payload = I.ipayload unit

(* The unindexed API is only the unit specialization of the indexed model. *)
let rec entries (nodes: list lref) : Tot (I.entries unit) (decreases nodes) =
  match nodes with
  | [] -> []
  | node :: rest -> (node, ()) :: entries rest

let of_unary (p: lref -> slprop) : payload = fun node () -> p node

let is_list_seg_with (p: payload) (prev cur endl: lref) (permission: perm)
                     (nodes: list lref) : slprop =
  I.is_list_seg_ix p prev cur endl permission (entries nodes)

let is_list_ring_with (p: payload) ([@@@mkey] head: lref) (permission: perm)
                      (nodes: list lref) : slprop =
  I.is_list_ring_ix p head permission (entries nodes)

let rec entries_append (front back: list lref)
  : Lemma (entries (front @ back) == entries front @ entries back)
    (decreases front) =
  match front with
  | [] -> ()
  | _ :: rest -> entries_append rest back

let rec entries_nodes (nodes: list lref)
  : Lemma (I.cells_of (entries nodes) == nodes) (decreases nodes) =
  match nodes with
  | [] -> ()
  | _ :: rest -> entries_nodes rest

let rec nodes_entries (es: I.entries unit)
  : Lemma (entries (I.cells_of es) == es) (decreases es) =
  match es with
  | [] -> ()
  | _ :: rest -> nodes_entries rest

ghost
fn ring_to_indexed (p: payload) (head: lref) (permission: perm) (nodes: list lref)
  requires is_list_ring_with p head permission nodes
  ensures I.is_list_ring_ix p head permission (entries nodes)
{
  unfold (is_list_ring_with p head permission nodes);
}

ghost
fn ring_from_indexed (p: payload) (head: lref) (permission: perm) (nodes: list lref)
  requires I.is_list_ring_ix p head permission (entries nodes)
  ensures is_list_ring_with p head permission nodes
{
  fold (is_list_ring_with p head permission nodes);
}

ghost
fn segment_to_indexed (p: payload) (prev cur endl: lref)
                     (permission: perm) (nodes: list lref)
  requires is_list_seg_with p prev cur endl permission nodes
  ensures I.is_list_seg_ix p prev cur endl permission (entries nodes)
{
  unfold (is_list_seg_with p prev cur endl permission nodes);
}

ghost
fn segment_from_indexed (p: payload) (prev cur endl: lref)
                       (permission: perm) (nodes: list lref)
  requires I.is_list_seg_ix p prev cur endl permission (entries nodes)
  ensures is_list_seg_with p prev cur endl permission nodes
{
  fold (is_list_seg_with p prev cur endl permission nodes);
}

let checked = unit

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
    pure (node == I.last_or head (entries (reveal front)))
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
    pure (position == I.last_or head (entries (reveal front))) **
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
    R.pts_to entry (B.mklink
      (I.first_or head (entries (reveal back)))
      (I.last_or head (entries (reveal front)))) **
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
    (exists* (next: lref). R.pts_to result (B.mklink next head)) **
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
