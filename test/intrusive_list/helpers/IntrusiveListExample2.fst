module IntrusiveListExample2
open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module R = Pulse.Lib.Reference
module N = Struct_list_node
module I = Struct_item2
module X = IntrusiveListIndexed
module Q = IntrusiveListItems

noeq type description = {
  priority: Int32.t;
  used: UInt32.t;
  samples: full_array_lspec UInt32.t 4;
  counter: ref UInt32.t;
  count: UInt32.t;
}

unfold let entries = X.entries description
unfold let item_ref = ref I.struct_item2
unfold let owner (node: X.lref) : item_ref = I.struct_item2__link_container node
unfold let node (item: item_ref) : GTot X.lref = I.struct_item2__link_1 item

unfold let make (priority: Int32.t) (used: UInt32.t)
                (samples: full_array_lspec UInt32.t 4)
                (counter: ref UInt32.t) (count: UInt32.t) : description = {
  priority = priority;
  used = used;
  samples = samples;
  counter = counter;
  count = count;
}

unfold let item_record (d: description) (link: N.struct_list_node) : I.struct_item2 = {
  I.struct_item2__priority = d.priority;
  I.struct_item2__used = d.used;
  I.struct_item2__samples = d.samples;
  I.struct_item2__processed = d.counter;
  I.struct_item2__link = link;
}

let owned ([@@@mkey] item: item_ref) (d: description) (link: N.struct_list_node) : slprop =
  R.pts_to item (item_record d link) ** R.pts_to d.counter d.count **
  pure (UInt32.v d.used <= 4)

let detached ([@@@mkey] item: item_ref) (d: description) : slprop =
  exists* (link: N.struct_list_node). owned item d link

(* The inline array and the separate caller-owned counter are both real resources. *)
let fields ([@@@mkey] item: item_ref) (d: description) : slprop =
  I.struct_item2__aux_raw_unfolded item 1.0R **
  R.pts_to (I.struct_item2__priority_1 item) d.priority **
  R.pts_to (I.struct_item2__used_1 item) d.used **
  array_pts_to (I.struct_item2__samples_1 item) 1.0R d.samples **
  R.pts_to (I.struct_item2__processed_1 item) d.counter **
  R.pts_to d.counter d.count ** pure (UInt32.v d.used <= 4)

let item_ipl ([@@@mkey] node: X.lref) (d: description) : slprop = fields (owner node) d

unfold let processed (d: description) : description =
  { d with count = UInt32.add_mod d.count 1ul }

let sample_at (d: description) (index: nat) : UInt32.t =
  if index < 4 then array_spec_idx d.samples index else 0ul

let processed_exact (d: description)
  : Lemma
    (requires UInt32.v d.count < 4294967295)
    (ensures UInt32.v (processed d).count == UInt32.v d.count + 1)
  = ()

ghost
fn processing_open (item: item_ref) (d: description) (link: N.struct_list_node)
  requires owned item d link
  ensures I.struct_item2__aux_raw_unfolded item 1.0R **
    R.pts_to (I.struct_item2__priority_1 item) d.priority **
    R.pts_to (I.struct_item2__used_1 item) d.used **
    array_pts_to (I.struct_item2__samples_1 item) 1.0R d.samples **
    R.pts_to (I.struct_item2__processed_1 item) d.counter **
    R.pts_to (I.struct_item2__link_1 item) link **
    R.pts_to d.counter d.count ** pure (UInt32.v d.used <= 4)
{
  unfold (owned item d link);
  I.struct_item2__aux_raw_unfold item (item_record d link);
}

ghost
fn processing_close (item: item_ref) (d: description) (link: N.struct_list_node)
  requires I.struct_item2__aux_raw_unfolded item 1.0R **
    R.pts_to (I.struct_item2__priority_1 item) d.priority **
    R.pts_to (I.struct_item2__used_1 item) d.used **
    array_pts_to (I.struct_item2__samples_1 item) 1.0R d.samples **
    R.pts_to (I.struct_item2__processed_1 item) d.counter **
    R.pts_to (I.struct_item2__link_1 item) link **
    R.pts_to d.counter (UInt32.add_mod d.count 1ul) ** pure (UInt32.v d.used <= 4)
  ensures owned item (processed d) link
{
  I.struct_item2__aux_raw_fold item d.priority d.used d.samples d.counter link;
  fold (owned item (processed d) link);
}

ghost
fn item_to_payload (item: item_ref) (d: description) (#link: N.struct_list_node)
  requires owned item d link
  ensures item_ipl (I.struct_item2__link_1 item) d **
    R.pts_to (I.struct_item2__link_1 item) link
{
  processing_open item d link;
  fold (fields item d);
  rewrite (fields item d) as (fields (owner (I.struct_item2__link_1 item)) d);
  fold (item_ipl (I.struct_item2__link_1 item) d);
}

ghost
fn payload_to_item (node: X.lref) (d: description) (#link: N.struct_list_node)
  requires item_ipl node d ** R.pts_to node link
  ensures owned (owner node) d link
{
  unfold (item_ipl node d);
  unfold (fields (owner node) d);
  rewrite (R.pts_to node link) as (R.pts_to (I.struct_item2__link_1 (owner node)) link);
  I.struct_item2__aux_raw_fold (owner node) d.priority d.used d.samples d.counter link;
  fold (owned (owner node) d link);
}

ghost
fn resource_roundtrip (item: item_ref) (d: description) (link: N.struct_list_node)
  requires owned item d link
  ensures owned item d link
{
  item_to_payload item d;
  payload_to_item (I.struct_item2__link_1 item) d;
  rewrite (owned (owner (I.struct_item2__link_1 item)) d link) as (owned item d link);
}

let value_rest ([@@@mkey] item: item_ref) (d: description) : slprop =
  R.pts_to (I.struct_item2__used_1 item) d.used **
  array_pts_to (I.struct_item2__samples_1 item) 1.0R d.samples **
  R.pts_to (I.struct_item2__processed_1 item) d.counter **
  R.pts_to d.counter d.count ** pure (UInt32.v d.used <= 4)

ghost
fn value_open (node: X.lref) (item: item_ref) (#d: description)
  requires item_ipl node d ** pure (item == owner node)
  ensures I.struct_item2__aux_raw_unfolded item 1.0R **
    R.pts_to (I.struct_item2__priority_1 item) d.priority ** value_rest item d
{
  unfold (item_ipl node d);
  rewrite (fields (owner node) d) as (fields item d);
  unfold (fields item d);
  fold (value_rest item d);
}

ghost
fn value_close (node: X.lref) (item: item_ref) (#d: description)
  requires I.struct_item2__aux_raw_unfolded item 1.0R **
    R.pts_to (I.struct_item2__priority_1 item) d.priority ** value_rest item d **
    pure (item == owner node)
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
  | None -> null
  | Some e -> owner (fst e)

ghost
fn capture (item: item_ref) (counter: ref UInt32.t) (d: description)
           (#count: UInt32.t) (#v: I.struct_item2)
  requires R.pts_to item v ** R.pts_to counter count **
    pure (UInt32.v d.used <= 4 /\ counter == d.counter /\ count == d.count /\
      v == item_record d v.I.struct_item2__link)
  ensures detached item d
{
  rewrite (R.pts_to counter count) as (R.pts_to d.counter d.count);
  rewrite (R.pts_to item v) as (R.pts_to item (item_record d v.I.struct_item2__link));
  fold (owned item d v.I.struct_item2__link);
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
    I.struct_item2__aux_raw_unfolded item 1.0R **
    R.pts_to (I.struct_item2__priority_1 item) d.priority **
    R.pts_to (I.struct_item2__used_1 item) d.used **
    array_pts_to (I.struct_item2__samples_1 item) 1.0R d.samples **
    R.pts_to (I.struct_item2__processed_1 item) d.counter **
    R.pts_to (I.struct_item2__link_1 item) link **
    R.pts_to d.counter d.count ** pure (UInt32.v d.used <= 4)
{
  unfold (detached item d);
  with link. assert (owned item d link);
  processing_open item d link;
}

ghost
fn prepare_item (item: item_ref) (entry: X.lref) (d: description)
                (#link: N.struct_list_node)
  requires I.struct_item2__aux_raw_unfolded item 1.0R **
    R.pts_to (I.struct_item2__priority_1 item) d.priority **
    R.pts_to (I.struct_item2__used_1 item) d.used **
    array_pts_to (I.struct_item2__samples_1 item) 1.0R d.samples **
    R.pts_to (I.struct_item2__processed_1 item) d.counter **
    R.pts_to entry link ** R.pts_to d.counter d.count **
    pure (UInt32.v d.used <= 4 /\ entry == node item)
  ensures item_ipl entry d ** R.pts_to_uninit entry
{
  fold (fields item d);
  rewrite (fields item d) as (fields (owner entry) d);
  fold (item_ipl entry d);
  Pulse.Lib.C.MaybeUninit.intro_maybe_some entry;
  Pulse.Lib.C.MaybeUninit.forget_maybe entry;
}

let pop_post (head: X.lref) (es: entries) (result: item_ref) : slprop =
  match es with
  | [] -> X.is_list_ring_ix item_ipl head 1.0R [] ** pure (result == null)
  | e :: rest ->
    X.is_list_ring_ix item_ipl head 1.0R rest **
    detached (owner (fst e)) (snd e) ** pure (result == owner (fst e))

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
      payload_to_item (fst e) (snd e);
      fold (detached (owner (fst e)) (snd e));
      fold (pop_post head es (owner node));
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
fn pop_one (head: X.lref) (item result: item_ref) (d: description) (rest: entries)
  requires pop_post head ((node item, d) :: rest) result
  ensures X.is_list_ring_ix item_ipl head 1.0R rest **
    detached item d ** pure (result == item)
{
  unfold (pop_post head ((node item, d) :: rest) result);
  rewrite (detached (owner (node item)) d) as (detached item d);
}

ghost
fn release_detached (item: item_ref) (counter: ref UInt32.t) (d: description)
  requires detached item d ** pure (counter == d.counter)
  ensures (exists* (link: N.struct_list_node). R.pts_to item (item_record d link)) **
    R.pts_to counter d.count
{
  unfold (detached item d);
  with link. assert (owned item d link);
  unfold (owned item d link);
  rewrite (R.pts_to d.counter d.count) as (R.pts_to counter d.count);
}
