module IntrusiveListContext
open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module B = IntrusiveListIndexed
module I = IntrusiveListIndexed
module R = Pulse.Lib.Reference

(* Dependent proof parameters travel together across the C annotation boundary. *)
noeq type context = {
  description_type: Type0;
  resource: I.ipayload description_type;
  entries: I.entries description_type;
}

noeq type insertion = {
  model: context;
  description: model.description_type;
}

noeq type cut = {
  model: context;
  head: B.lref;
  front: I.entries model.description_type;
  back: I.entries model.description_type;
  description: model.description_type;
}

noeq type validation = {
  model: context;
  head: B.lref;
  front: I.entries model.description_type;
  back: I.entries model.description_type;
}

noeq type movement = {
  source: context;
  destination_entries: I.entries source.description_type;
}

unfold let make (#a: Type0) (resource: I.ipayload a) (entries: I.entries a) : context = {
  description_type = a;
  resource = resource;
  entries = entries;
}

unfold let with_entries (ctx: context) (entries: I.entries ctx.description_type) : context =
  make ctx.resource entries

let ring (ctx: context) ([@@@mkey] head: B.lref) : slprop =
  I.is_list_ring_ix ctx.resource head 1.0R ctx.entries

let init_pre (ctx: context) (head: B.lref) : slprop =
  R.pts_to_uninit head ** pure (ctx.entries == [])

let empty_post (ctx: context) (head: B.lref) (empty: bool) : slprop =
  ring ctx head ** pure (empty <==> ctx.entries == [])

let insert_pre (ctx: insertion) (head entry: B.lref) : slprop =
  ring ctx.model head ** R.pts_to_uninit entry **
  ctx.model.resource entry ctx.description

let insert_head_post (ctx: insertion) (head entry: B.lref) : slprop =
  I.is_list_ring_ix ctx.model.resource head 1.0R
    ((entry, ctx.description) :: ctx.model.entries)

let insert_tail_post (ctx: insertion) (head entry: B.lref) : slprop =
  I.is_list_ring_ix ctx.model.resource head 1.0R
    (ctx.model.entries @ [(entry, ctx.description)])

let insert_after_pre (ctx: cut) (position entry: B.lref) : slprop =
  ring ctx.model ctx.head **
  pure (ctx.model.entries == ctx.front @ ctx.back) **
  pure (position == I.last_or ctx.head ctx.front) **
  R.pts_to_uninit entry ** ctx.model.resource entry ctx.description

let insert_after_post (ctx: cut) (entry: B.lref) : slprop =
  I.is_list_ring_ix ctx.model.resource ctx.head 1.0R
    (ctx.front @ ((entry, ctx.description) :: ctx.back))

let remove_pre (ctx: cut) (entry: B.lref) : slprop =
  ring ctx.model ctx.head **
  pure (ctx.model.entries == ctx.front @ ((entry, ctx.description) :: ctx.back))

let remove_post (ctx: cut) (entry: B.lref) (empty: bool) : slprop =
  I.is_list_ring_ix ctx.model.resource ctx.head 1.0R (ctx.front @ ctx.back) **
  R.pts_to entry (B.mklink
    (I.first_or ctx.head ctx.back) (I.last_or ctx.head ctx.front)) **
  ctx.model.resource entry ctx.description **
  pure (empty <==> ctx.front @ ctx.back == [])

let remove_head_pre (ctx: context) (head: B.lref) : slprop =
  ring ctx head ** pure (ctx.entries =!= [])

let remove_head_post (ctx: context) (head result: B.lref) : slprop =
  match ctx.entries with
  | [] -> pure False
  | (node, description) :: rest ->
    I.is_list_ring_ix ctx.resource head 1.0R rest **
    (exists* (next: B.lref). R.pts_to result (B.mklink next head)) **
    ctx.resource result description ** pure (result == node)

let validation_pre (ctx: validation) (node: B.lref) : slprop =
  ring ctx.model ctx.head **
  pure (ctx.model.entries == ctx.front @ ctx.back) **
  pure (node == I.last_or ctx.head ctx.front)

let move_pre (ctx: movement) (source destination: B.lref) : slprop =
  ring ctx.source source **
  I.is_list_ring_ix ctx.source.resource destination 1.0R ctx.destination_entries

let move_post (ctx: movement) (source destination: B.lref) : slprop =
  I.is_list_ring_ix ctx.source.resource source 1.0R [] **
  I.is_list_ring_ix ctx.source.resource destination 1.0R
    (ctx.destination_entries @ ctx.source.entries)

ghost
fn prepare_ring (ctx: context) (head: B.lref)
  requires I.is_list_ring_ix ctx.resource head 1.0R ctx.entries
  ensures ring ctx head
{
  fold (ring ctx head);
}

ghost
fn finish_ring (ctx: context) (head: B.lref)
  requires ring ctx head
  ensures I.is_list_ring_ix ctx.resource head 1.0R ctx.entries
{
  unfold (ring ctx head);
}

ghost
fn prepare_init (ctx: context) (head: B.lref)
  requires R.pts_to_uninit head ** pure (ctx.entries == [])
  ensures init_pre ctx head
{
  fold (init_pre ctx head);
}

ghost
fn prepare_empty (#a: Type0) (p: I.ipayload a) (head: B.lref) (es: I.entries a)
  requires I.is_list_ring_ix p head 1.0R es
  ensures ring (make p es) head
{
  prepare_ring (make p es) head;
}

ghost
fn finish_empty (#a: Type0) (p: I.ipayload a) (head: B.lref) (es: I.entries a)
                (#result: bool)
  requires empty_post (make p es) head result
  ensures I.is_list_ring_ix p head 1.0R es ** pure (result <==> es == [])
{
  unfold (empty_post (make p es) head result);
  finish_ring (make p es) head;
}

ghost
fn prepare_pop (#a: Type0) (p: I.ipayload a) (head: B.lref) (es: I.entries a)
  requires I.is_list_ring_ix p head 1.0R es ** pure (es =!= [])
  ensures remove_head_pre (make p es) head
{
  prepare_ring (make p es) head;
  fold (remove_head_pre (make p es) head);
}

unfold let validation_of (#a: Type0) (p: I.ipayload a) (head: B.lref)
                  (front back: I.entries a) : validation = {
  model = make p (front @ back);
  head = head;
  front = front;
  back = back;
}

ghost
fn prepare_validation (#a: Type0) (p: I.ipayload a) (head node: B.lref)
                      (front back: I.entries a)
  requires I.is_list_ring_ix p head 1.0R (front @ back) **
    pure (node == I.last_or head front)
  ensures validation_pre (validation_of p head front back) node
{
  prepare_ring (make p (front @ back)) head;
  fold (validation_pre (validation_of p head front back) node);
}

ghost
fn finish_validation (#a: Type0) (p: I.ipayload a) (head node: B.lref)
                     (front back: I.entries a)
  requires validation_pre (validation_of p head front back) node
  ensures I.is_list_ring_ix p head 1.0R (front @ back)
{
  unfold (validation_pre (validation_of p head front back) node);
  finish_ring (make p (front @ back)) head;
}

unfold let movement_of (#a: Type0) (p: I.ipayload a) (source destination: I.entries a)
  : movement = {
  source = make p source;
  destination_entries = destination;
}

ghost
fn prepare_move (#a: Type0) (p: I.ipayload a) (source destination: B.lref)
                (source_entries destination_entries: I.entries a)
  requires I.is_list_ring_ix p source 1.0R source_entries **
    I.is_list_ring_ix p destination 1.0R destination_entries
  ensures move_pre (movement_of p source_entries destination_entries) source destination
{
  prepare_ring (make p source_entries) source;
  fold (move_pre (movement_of p source_entries destination_entries) source destination);
}

ghost
fn finish_move (#a: Type0) (p: I.ipayload a) (source destination: B.lref)
               (source_entries destination_entries: I.entries a)
  requires move_post (movement_of p source_entries destination_entries) source destination
  ensures I.is_list_ring_ix p source 1.0R [] **
    I.is_list_ring_ix p destination 1.0R (destination_entries @ source_entries)
{
  unfold (move_post (movement_of p source_entries destination_entries) source destination);
}
