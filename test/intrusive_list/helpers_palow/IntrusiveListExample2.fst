module IntrusiveListExample2

(* The payload owns metadata, the inline samples, and a separate counter cell.
   Detached ownership reunites those resources with the link for sample processing. *)

open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module R = IntrusiveListNodeRef
module IR = IntrusiveListItemRefs
module N = Struct_list_node
module I = Struct_item2
module X = IntrusiveListIndexed
module Q = IntrusiveListItems
module Seq = FStar.Seq

noeq type description = {
  priority: Int32.t;
  used: UInt32.t;
  samples: IR.samples_t;
  counter: R.ref UInt32.t;
  count: UInt32.t;
}

unfold let entries = X.entries description
(* The four inline samples, written as a list. Each model has its own way of
   spelling an array's contents, so the C names this instead. *)
unfold let samples_of (l: list UInt32.t { List.Tot.length l == 4 }) : IR.samples_t =
  Seq.seq_of_list l

unfold let item_ref = R.ref I.struct_item2
unfold let owner (node: X.lref) : item_ref = IR.item2_container node
unfold let node (item: item_ref) : GTot X.lref = IR.item2_link_1 item

unfold let make (priority: Int32.t) (used: UInt32.t)
                (samples: IR.samples_t)
                (counter: R.ref UInt32.t) (count: UInt32.t) : description = {
  priority = priority;
  used = used;
  samples = samples;
  counter = counter;
  count = count;
}

unfold let item_record (d: description) (link: N.struct_list_node) : I.struct_item2 = {
  I.fld_priority = d.priority;
  I.fld_used = d.used;
  I.fld_samples = d.samples;
  I.fld_processed = d.counter;
  I.fld_link = link;
}

let owned ([@@@mkey] item: item_ref) (d: description) (link: N.struct_list_node) : slprop =
  IR.item2_pts_to item (item_record d link) ** IR.u32_pts_to d.counter d.count **
  pure (UInt32.v d.used <= 4)

let detached ([@@@mkey] item: item_ref) (d: description) : slprop =
  exists* (link: N.struct_list_node). owned item d link

(* The inline array and the separate caller-owned counter are both real resources. *)
let fields ([@@@mkey] item: item_ref) (d: description) : slprop =
  IR.item2_unfolded item 1.0R **
  IR.item2_priority (item) d.priority **
  IR.item2_used (item) d.used **
  IR.item2_samples item d.samples **
  IR.item2_processed (item) d.counter **
  IR.u32_pts_to d.counter d.count ** pure (UInt32.v d.used <= 4)

(* See `IntrusiveListItemRefs.item2_embedded`: recovering the item from its
   link is arithmetic here rather than an axiom, so the fact that makes the
   recovery meaningful has to be owned alongside the fields. *)
let item_ipl ([@@@mkey] node: X.lref) (d: description) : slprop =
  fields (owner node) d ** pure (IR.item2_embedded node)

unfold let processed (d: description) : description =
  { d with count = UInt32.add_mod d.count 1ul }

(* Total specification accessor; C processing requires index < used <= 4. *)
let sample_at (d: description) (index: nat) : UInt32.t =
  if index < 4 then Seq.index d.samples index else 0ul

let processed_exact (d: description)
  : Lemma
    (requires UInt32.v d.count < 4294967295)
    (ensures UInt32.v (processed d).count == UInt32.v d.count + 1)
  = ()

(* Where the current model hands out one reference per field, Palow hands out
   the object: a field access is an offset from the object's address, and the
   emitter writes the `focus`/`unfocus` pair around it. So opening the payload
   for processing is just unfolding the abstraction, and the counter -- which
   is a separate cell, not a field -- travels alongside as before. *)
ghost
fn processing_open (item: item_ref) (d: description) (link: N.struct_list_node)
  requires owned item d link
  ensures IR.item2_pts_to item (item_record d link) **
    IR.u32_pts_to d.counter d.count ** pure (UInt32.v d.used <= 4)
{
  unfold (owned item d link);
}

ghost
fn processing_close (item: item_ref) (d: description) (link: N.struct_list_node)
  requires IR.item2_pts_to item (item_record d link) **
    IR.u32_pts_to d.counter (UInt32.add_mod d.count 1ul) ** pure (UInt32.v d.used <= 4)
  ensures owned item (processed d) link
{
  fold (owned item (processed d) link);
}

ghost
fn item_to_payload (item: item_ref) (d: description) (#link: N.struct_list_node)
  requires owned item d link
  ensures item_ipl (IR.item2_link_1 item) d **
    IR.item2_link (item) link
{
  unfold (owned item d link);
  IR.item2_unfold item (item_record d link);
  fold (fields item d);
  rewrite (fields item d) as (fields (owner (IR.item2_link_1 item)) d);
  fold (item_ipl (IR.item2_link_1 item) d);
}

ghost
fn payload_to_item (node: X.lref) (d: description) (#link: N.struct_list_node)
  requires item_ipl node d ** R.pts_to node link
  ensures owned (owner node) d link
{
  unfold (item_ipl node d);
  unfold (fields (owner node) d);
  rewrite (R.pts_to node link) as (IR.item2_link ((owner node)) link);
  IR.item2_fold (owner node) d.priority d.used d.samples d.counter link;
  fold (owned (owner node) d link);
}

(* Check that splitting/rejoining array and counter ownership preserves the item. *)
ghost
fn resource_roundtrip (item: item_ref) (d: description) (link: N.struct_list_node)
  requires owned item d link
  ensures owned item d link
{
  item_to_payload item d;
  payload_to_item (IR.item2_link_1 item) d;
  rewrite (owned (owner (IR.item2_link_1 item)) d link) as (owned item d link);
}

let value_rest ([@@@mkey] item: item_ref) (d: description) : slprop =
  IR.item2_used (item) d.used **
  IR.item2_samples item d.samples **
  IR.item2_processed (item) d.counter **
  IR.u32_pts_to d.counter d.count ** pure (UInt32.v d.used <= 4)

ghost
fn value_open (node: X.lref) (item: item_ref) (#d: description)
  requires item_ipl node d ** pure (item == owner node)
  ensures IR.item2_unfolded item 1.0R **
    IR.item2_priority (item) d.priority ** value_rest item d
{
  unfold (item_ipl node d);
  rewrite (fields (owner node) d) as (fields item d);
  unfold (fields item d);
  fold (value_rest item d);
}

ghost
fn value_close (node: X.lref) (item: item_ref) (#d: description)
  requires IR.item2_unfolded item 1.0R **
    IR.item2_priority (item) d.priority ** value_rest item d **
    pure (item == owner node /\ IR.item2_embedded node)
  ensures item_ipl node d
{
  unfold (value_rest item d);
  fold (fields item d);
  rewrite (fields item d) as (fields (owner node) d);
  fold (item_ipl node d);
}

let matches_priority (key: Int32.t) (_node: X.lref) (d: description) : GTot bool =
  d.priority == key

let priority_le (x y: description) : GTot bool =
  Int32.v x.priority <= Int32.v y.priority

let priority_order () : Lemma (X.total_preorder priority_le) = ()

let first_match (key: Int32.t) (es: entries) : GTot item_ref =
  match X.first_match_entry (matches_priority key) es with
  | None -> R.null
  | Some e -> owner (fst e)

ghost
fn capture (item: item_ref) (counter: R.ref UInt32.t) (d: description)
           (#count: UInt32.t) (#v: I.struct_item2)
  requires IR.item2_pts_to item v ** IR.u32_pts_to counter count **
    pure (UInt32.v d.used <= 4 /\ counter == d.counter /\ count == d.count /\
      v == item_record d v.I.fld_link)
  ensures detached item d
{
  rewrite (IR.u32_pts_to counter count) as (IR.u32_pts_to d.counter d.count);
  rewrite (IR.item2_pts_to item v) as (IR.item2_pts_to item (item_record d v.I.fld_link));
  fold (owned item d v.I.fld_link);
  fold (detached item d);
}

ghost
fn open_detached (item: item_ref) (d: description)
  requires detached item d
  ensures exists* (link: N.struct_list_node). owned item d link
{
  unfold (detached item d);
}

ghost
fn close_detached (item: item_ref) (d: description) (#link: N.struct_list_node)
  requires owned item d link
  ensures detached item d
{
  fold (detached item d);
}

ghost
fn open_for_insert (item: item_ref) (d: description)
  requires detached item d
  ensures exists* (link: N.struct_list_node).
    IR.item2_unfolded item 1.0R **
    IR.item2_priority (item) d.priority **
    IR.item2_used (item) d.used **
    IR.item2_samples item d.samples **
    IR.item2_processed (item) d.counter **
    IR.item2_link (item) link **
    IR.u32_pts_to d.counter d.count ** pure (UInt32.v d.used <= 4)
{
  unfold (detached item d);
  with link. assert (owned item d link);
  unfold (owned item d link);
  IR.item2_unfold item (item_record d link);
}

ghost
fn prepare_item (item: item_ref) (entry: X.lref) (d: description)
                (#link: N.struct_list_node)
  requires IR.item2_unfolded item 1.0R **
    IR.item2_priority (item) d.priority **
    IR.item2_used (item) d.used **
    IR.item2_samples item d.samples **
    IR.item2_processed (item) d.counter **
    R.pts_to entry link ** IR.u32_pts_to d.counter d.count **
    pure (UInt32.v d.used <= 4 /\ entry == node item)
  ensures item_ipl entry d ** R.pts_to_uninit entry
{
  fold (fields item d);
  rewrite (fields item d) as (fields (owner entry) d);
  fold (item_ipl entry d);
  R.forget entry;
}

let pop_post (head: X.lref) (es: entries) (result: item_ref) : slprop =
  match es with
  | [] -> X.is_list_ring_ix item_ipl head 1.0R [] ** pure (result == R.null)
  | e :: rest ->
    X.is_list_ring_ix item_ipl head 1.0R rest **
    detached (owner (fst e)) (snd e) ** pure (result == owner (fst e))

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
      payload_to_item (fst e) (snd e);
      fold (detached (owner (fst e)) (snd e));
      fold (pop_post head es (owner node));
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
fn pop_one (head: X.lref) (item result: item_ref) (d: description) (rest: entries)
  requires pop_post head ((node item, d) :: rest) result
  ensures X.is_list_ring_ix item_ipl head 1.0R rest **
    detached item d ** pure (result == item)
{
  unfold (pop_post head ((node item, d) :: rest) result);
  rewrite (detached (owner (node item)) d) as (detached item d);
}

ghost
fn release_detached (item: item_ref) (counter: R.ref UInt32.t) (d: description)
  requires detached item d ** pure (counter == d.counter)
  ensures (exists* (link: N.struct_list_node). IR.item2_pts_to item (item_record d link)) **
    IR.u32_pts_to counter d.count
{
  unfold (detached item d);
  with link. assert (owned item d link);
  unfold (owned item d link);
  rewrite (IR.u32_pts_to d.counter d.count) as (IR.u32_pts_to counter d.count);
}
