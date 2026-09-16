module IntrusiveListContext

(* C-facing forms of the indexed contracts. Erased records bundle dependent
   parameters for named C ghost types; the helpers only prepare/restore ownership,
   not execute list mutations. F* proofs can still pass P and entries directly. *)

open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module X = IntrusiveListIndexed
module R = Pulse.Lib.Reference

(* Dependent proof parameters travel together across the C annotation boundary. *)
noeq type context = {
  description_type: Type0;
  resource: X.ipayload description_type;
  entries: X.entries description_type;
}

noeq type insertion = {
  model: context;
  description: model.description_type;
}

noeq type cut = {
  model: context;
  head: X.lref;
  front: X.entries model.description_type;
  back: X.entries model.description_type;
  description: model.description_type;
}

noeq type validation = {
  model: context;
  head: X.lref;
  front: X.entries model.description_type;
  back: X.entries model.description_type;
}

noeq type movement = {
  source: context;
  destination_entries: X.entries source.description_type;
}

unfold let make (#a: Type0) (resource: X.ipayload a) (entries: X.entries a) : context = {
  description_type = a;
  resource = resource;
  entries = entries;
}

unfold let with_entries (ctx: context) (entries: X.entries ctx.description_type) : context =
  make ctx.resource entries

let ring (ctx: context) ([@@@mkey] head: X.lref) : slprop =
  X.is_list_ring_ix ctx.resource head 1.0R ctx.entries

let init_pre (ctx: context) (head: X.lref) : slprop =
  R.pts_to_uninit head ** pure (ctx.entries == [])

let empty_post (ctx: context) (head: X.lref) (empty: bool) : slprop =
  ring ctx head ** pure (empty <==> ctx.entries == [])

let insert_pre (ctx: insertion) (head entry: X.lref) : slprop =
  ring ctx.model head ** R.pts_to_uninit entry **
  ctx.model.resource entry ctx.description

let insert_head_post (ctx: insertion) (head entry: X.lref) : slprop =
  X.is_list_ring_ix ctx.model.resource head 1.0R
    ((entry, ctx.description) :: ctx.model.entries)

let insert_tail_post (ctx: insertion) (head entry: X.lref) : slprop =
  X.is_list_ring_ix ctx.model.resource head 1.0R
    (ctx.model.entries @ [(entry, ctx.description)])

let insert_after_pre (ctx: cut) (position entry: X.lref) : slprop =
  ring ctx.model ctx.head **
  pure (ctx.model.entries == ctx.front @ ctx.back) **
  pure (position == X.last_or ctx.head ctx.front) **
  R.pts_to_uninit entry ** ctx.model.resource entry ctx.description

let insert_after_post (ctx: cut) (entry: X.lref) : slprop =
  X.is_list_ring_ix ctx.model.resource ctx.head 1.0R
    (ctx.front @ ((entry, ctx.description) :: ctx.back))

let remove_pre (ctx: cut) (entry: X.lref) : slprop =
  ring ctx.model ctx.head **
  pure (ctx.model.entries == ctx.front @ ((entry, ctx.description) :: ctx.back))

let remove_post (ctx: cut) (entry: X.lref) (empty: bool) : slprop =
  X.is_list_ring_ix ctx.model.resource ctx.head 1.0R (ctx.front @ ctx.back) **
  R.pts_to entry (X.mklink
    (X.first_or ctx.head ctx.back) (X.last_or ctx.head ctx.front)) **
  ctx.model.resource entry ctx.description **
  pure (empty <==> ctx.front @ ctx.back == [])

let remove_head_pre (ctx: context) (head: X.lref) : slprop =
  ring ctx head ** pure (ctx.entries =!= [])

let remove_head_post (ctx: context) (head result: X.lref) : slprop =
  match ctx.entries with
  | [] -> pure False
  | (node, description) :: rest ->
    X.is_list_ring_ix ctx.resource head 1.0R rest **
    (exists* (next: X.lref). R.pts_to result (X.mklink next head)) **
    ctx.resource result description ** pure (result == node)

let validation_pre (ctx: validation) (node: X.lref) : slprop =
  ring ctx.model ctx.head **
  pure (ctx.model.entries == ctx.front @ ctx.back) **
  pure (node == X.last_or ctx.head ctx.front)

let move_pre (ctx: movement) (source destination: X.lref) : slprop =
  ring ctx.source source **
  X.is_list_ring_ix ctx.source.resource destination 1.0R ctx.destination_entries

let move_post (ctx: movement) (source destination: X.lref) : slprop =
  X.is_list_ring_ix ctx.source.resource source 1.0R [] **
  X.is_list_ring_ix ctx.source.resource destination 1.0R
    (ctx.destination_entries @ ctx.source.entries)

ghost
fn prepare_ring (ctx: context) (head: X.lref)
  requires X.is_list_ring_ix ctx.resource head 1.0R ctx.entries
  ensures ring ctx head
{
  fold (ring ctx head);
}

ghost
fn finish_ring (ctx: context) (head: X.lref)
  requires ring ctx head
  ensures X.is_list_ring_ix ctx.resource head 1.0R ctx.entries
{
  unfold (ring ctx head);
}

(* Raw storage alone cannot determine the payload; fix its context before calling C. *)
ghost
fn prepare_init (ctx: context) (head: X.lref)
  requires R.pts_to_uninit head ** pure (ctx.entries == [])
  ensures init_pre ctx head
{
  fold (init_pre ctx head);
}

ghost
fn prepare_empty (#a: Type0) (p: X.ipayload a) (head: X.lref) (es: X.entries a)
  requires X.is_list_ring_ix p head 1.0R es
  ensures ring (make p es) head
{
  prepare_ring (make p es) head;
}

ghost
fn finish_empty (#a: Type0) (p: X.ipayload a) (head: X.lref) (es: X.entries a)
                (#result: bool)
  requires empty_post (make p es) head result
  ensures X.is_list_ring_ix p head 1.0R es ** pure (result <==> es == [])
{
  unfold (empty_post (make p es) head result);
  finish_ring (make p es) head;
}

ghost
fn prepare_pop (#a: Type0) (p: X.ipayload a) (head: X.lref) (es: X.entries a)
  requires X.is_list_ring_ix p head 1.0R es ** pure (es =!= [])
  ensures remove_head_pre (make p es) head
{
  prepare_ring (make p es) head;
  fold (remove_head_pre (make p es) head);
}

unfold let validation_of (#a: Type0) (p: X.ipayload a) (head: X.lref)
                  (front back: X.entries a) : validation = {
  model = make p (front @ back);
  head = head;
  front = front;
  back = back;
}

ghost
fn prepare_validation (#a: Type0) (p: X.ipayload a) (head node: X.lref)
                      (front back: X.entries a)
  requires X.is_list_ring_ix p head 1.0R (front @ back) **
    pure (node == X.last_or head front)
  ensures validation_pre (validation_of p head front back) node
{
  prepare_ring (make p (front @ back)) head;
  fold (validation_pre (validation_of p head front back) node);
}

ghost
fn finish_validation (#a: Type0) (p: X.ipayload a) (head node: X.lref)
                     (front back: X.entries a)
  requires validation_pre (validation_of p head front back) node
  ensures X.is_list_ring_ix p head 1.0R (front @ back)
{
  unfold (validation_pre (validation_of p head front back) node);
  finish_ring (make p (front @ back)) head;
}

unfold let movement_of (#a: Type0) (p: X.ipayload a) (source destination: X.entries a)
  : movement = {
  source = make p source;
  destination_entries = destination;
}

ghost
fn prepare_move (#a: Type0) (p: X.ipayload a) (source destination: X.lref)
                (source_entries destination_entries: X.entries a)
  requires X.is_list_ring_ix p source 1.0R source_entries **
    X.is_list_ring_ix p destination 1.0R destination_entries
  ensures move_pre (movement_of p source_entries destination_entries) source destination
{
  prepare_ring (make p source_entries) source;
  fold (move_pre (movement_of p source_entries destination_entries) source destination);
}

ghost
fn finish_move (#a: Type0) (p: X.ipayload a) (source destination: X.lref)
               (source_entries destination_entries: X.entries a)
  requires move_post (movement_of p source_entries destination_entries) source destination
  ensures X.is_list_ring_ix p source 1.0R [] **
    X.is_list_ring_ix p destination 1.0R (destination_entries @ source_entries)
{
  unfold (move_post (movement_of p source_entries destination_entries) source destination);
}
