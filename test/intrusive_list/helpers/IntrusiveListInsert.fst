module IntrusiveListInsert
open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module R = Pulse.Lib.Reference
module N = Struct_list_node
module L = IntrusiveListIndexed
module X = IntrusiveListIndexed
module C = IntrusiveListContext
module T = Pulse.Lib.Trade

let inv (#a: Type0) (p: L.ipayload a) (le: X.order a)
        (head pos entry: L.lref) (description: a) (es: X.entries a)
        (stopped: bool) : slprop =
  exists* (front back: X.entries a).
    X.split p head pos front back **
    pure (front @ back == es) **
    pure (X.insert le entry description es == front @ X.insert le entry description back) **
    pure (stopped ==> X.insert le entry description back == (entry, description) :: back)

let mid (#a: Type0) (p: L.ipayload a) (le: X.order a)
        (head pos entry: L.lref) (description: a) (es: X.entries a)
        (current: a) (v: N.struct_list_node) : slprop =
  exists* (front back: X.entries a).
    X.cursor_rest p head pos front current back v **
    pure (front @ ((pos, current) :: back) == es) **
    pure (X.insert le entry description es ==
      front @ X.insert le entry description ((pos, current) :: back))

let ready (#a: Type0) (p: L.ipayload a) (le: X.order a)
          (head pos entry: L.lref) (description: a) (es: X.entries a) : slprop =
  exists* (front back: X.entries a).
    L.is_list_ring_ix p head 1.0R (front @ back) **
    pure (front @ back == es) **
    pure (pos == L.first_or head back) **
    pure ((pos == head) <==> (back == [])) **
    pure (X.insert le entry description es == front @ ((entry, description) :: back))

ghost
fn start (#a: Type0) (p: L.ipayload a) (le: X.order a)
         (head pos entry: L.lref) (description: a) (es: X.entries a)
         (#hv: N.struct_list_node)
  requires R.pts_to head hv ** X.head_rest p head es hv ** pure (pos == L.lnext hv)
  ensures inv p le head pos entry description es false
{
  X.cursor_start p head pos es;
  fold (inv p le head pos entry description es false);
}

ghost
fn expose (#a: Type0) (p: L.ipayload a) (le: X.order a)
          (head pos entry: L.lref) (description: a) (es: X.entries a)
          (#stopped: bool)
  requires inv p le head pos entry description es stopped ** pure (pos =!= head)
  ensures exists* (current: a) (v: N.struct_list_node).
    R.pts_to pos v ** p pos current ** mid p le head pos entry description es current v
{
  unfold (inv p le head pos entry description es stopped);
  with front back. assert (X.split p head pos front back);
  X.split_facts p head pos front back;
  let e = Cons?.hd back;
  let rest = Cons?.tl back;
  rewrite (X.split p head pos front back) as (X.split p head pos front (e :: rest));
  X.cursor_expose p head pos front e rest;
  with v. assert (R.pts_to pos v);
  fold (mid p le head pos entry description es (snd e) v);
}

ghost
fn mid_repack (#a: Type0) (p: L.ipayload a) (le: X.order a)
              (head pos entry: L.lref) (description: a) (es: X.entries a)
              (#current: a) (#v: N.struct_list_node)
  requires mid p le head pos entry description es current v
  ensures mid p le head pos entry description es current (L.mklink (L.lnext v) (L.lprev v))
{
  rewrite (mid p le head pos entry description es current v)
    as (mid p le head pos entry description es current (L.mklink (L.lnext v) (L.lprev v)));
}

ghost
fn step (#a: Type0) (p: L.ipayload a) (le: X.order a)
        (head pos next entry: L.lref) (description: a) (es: X.entries a)
        (#current: a) (#v: N.struct_list_node)
  requires R.pts_to pos v ** p pos current **
    mid p le head pos entry description es current v **
    pure (next == L.lnext v) ** pure (le current description)
  ensures inv p le head next entry description es false
{
  unfold (mid p le head pos entry description es current v);
  with front back. assert (X.cursor_rest p head pos front current back v);
  X.cursor_advance p head pos front current back;
  FStar.List.Tot.Properties.append_assoc front [(pos, current)] back;
  FStar.List.Tot.Properties.append_assoc front [(pos, current)]
    (X.insert le entry description back);
  rewrite (X.split p head (L.lnext v) (front @ [(pos, current)]) back)
    as (X.split p head next (front @ [(pos, current)]) back);
  fold (inv p le head next entry description es false);
}

(* The flag records the comparison while its concrete payload is exposed. *)
ghost
fn unexpose (#a: Type0) (p: L.ipayload a) (le: X.order a)
            (head pos entry: L.lref) (description: a) (es: X.entries a)
            (stopped: bool) (#current: a) (#v: N.struct_list_node)
  requires R.pts_to pos v ** p pos current **
    mid p le head pos entry description es current v **
    pure (stopped ==> not (le current description))
  ensures inv p le head pos entry description es stopped
{
  unfold (mid p le head pos entry description es current v);
  with front back. assert (X.cursor_rest p head pos front current back v);
  X.cursor_restore p head pos front current back;
  fold (inv p le head pos entry description es stopped);
}

ghost
fn settle (#a: Type0) (p: L.ipayload a) (le: X.order a)
          (head pos entry: L.lref) (description: a) (es: X.entries a)
          (#stopped: bool)
  requires inv p le head pos entry description es stopped **
    pure (stopped \/ pos == head)
  ensures ready p le head pos entry description es
{
  unfold (inv p le head pos entry description es stopped);
  with front back. assert (X.split p head pos front back);
  X.split_facts p head pos front back;
  X.split_close p head pos front back;
  fold (ready p le head pos entry description es);
}

ghost
fn found (#a: Type0) (p: L.ipayload a) (le: X.order a)
         (head pos entry: L.lref) (description: a) (es: X.entries a)
         (#current: a) (#v: N.struct_list_node)
  requires R.pts_to pos v ** p pos current **
    mid p le head pos entry description es current v **
    pure (not (le current description))
  ensures ready p le head pos entry description es
{
  unexpose p le head pos entry description es true;
  settle p le head pos entry description es;
}

[@@pulse_intro]
ghost
fn end_scan (#a: Type0) (p: L.ipayload a) (le: X.order a)
            (head pos entry: L.lref) (description: a) (es: X.entries a)
            (#stopped: bool)
  requires inv p le head pos entry description es stopped ** pure (pos == head)
  ensures ready p le head pos entry description es
{
  settle p le head pos entry description es;
}

let post (#a: Type0) (p: L.ipayload a) (le: X.order a)
         (head entry: L.lref) (description: a) (es: X.entries a) : slprop =
  L.is_list_ring_ix p head 1.0R (X.insert le entry description es) **
  pure (X.sorted le (X.insert le entry description es))

ghost
fn post_normalize (#a: Type0) (p: L.ipayload a) (le: X.order a)
                  (head entry: L.lref) (description: a) (es: X.entries a)
                  (#old_head #old_entry: L.lref)
  requires post p le old_head old_entry description es **
    pure (old_head == head /\ old_entry == entry)
  ensures post p le head entry description es
{
  rewrite (post p le old_head old_entry description es)
    as (post p le head entry description es);
}

[@@pulse_intro]
ghost
fn post_elim (#a: Type0) (p: L.ipayload a) (le: X.order a)
             (head entry: L.lref) (description: a) (es: X.entries a)
             (#old_head #old_entry: L.lref)
  requires post p le old_head old_entry description es **
    pure (old_head == head /\ old_entry == entry)
  ensures L.is_list_ring_ix p head 1.0R (X.insert le entry description es) **
    pure (X.sorted le (X.insert le entry description es))
{
  post_normalize p le head entry description es;
  unfold (post p le head entry description es);
}

let pending (#a: Type0) (p: L.ipayload a) (le: X.order a)
            (head entry: L.lref) (description: a) (es: X.entries a)
            (front back: X.entries a) : slprop =
  pure (X.insert le entry description es == front @ ((entry, description) :: back))

unfold let insertion_context (#a: Type0) (p: L.ipayload a)
                      (description: a) (es: X.entries a) : C.insertion = {
  model = {
    description_type = a;
    resource = p;
    entries = es;
  };
  description = description;
}

unfold let cut_context (#a: Type0) (p: L.ipayload a) (head: L.lref)
                (description: a) (front back: X.entries a) : C.cut = {
  model = {
    description_type = a;
    resource = p;
    entries = front @ back;
  };
  head = head;
  front = front;
  back = back;
  description = description;
}

ghost
fn prepare_cut (#a: Type0) (p: L.ipayload a) (le: X.order a)
               (head entry: L.lref) (description: a) (es: X.entries a)
               (front back: X.entries a)
  requires L.is_list_ring_ix p head 1.0R (front @ back) **
    R.pts_to_uninit entry ** p entry description **
    pure (X.insert le entry description es == front @ ((entry, description) :: back))
  ensures C.insert_after_pre (cut_context p head description front back)
    (L.last_or head front) entry **
    pending p le head entry description es front back
{
  C.prepare_ring (cut_context p head description front back).model head;
  fold (C.insert_after_pre (cut_context p head description front back)
    (L.last_or head front) entry);
  fold (pending p le head entry description es front back);
}

ghost
fn prepare_tail (#a: Type0) (p: L.ipayload a) (le: X.order a)
                (head pos entry: L.lref) (description: a) (es: X.entries a)
  requires ready p le head pos entry description es **
    R.pts_to_uninit entry ** p entry description **
    pure (pos == head)
  ensures C.insert_pre (insertion_context p description es) head entry **
    pending p le head entry description es es []
{
  unfold (ready p le head pos entry description es);
  with front back. assert (L.is_list_ring_ix p head 1.0R (front @ back));
  FStar.List.Tot.Properties.append_l_nil front;
  rewrite (L.is_list_ring_ix p head 1.0R (front @ back))
    as (L.is_list_ring_ix p head 1.0R es);
  C.prepare_ring (insertion_context p description es).model head;
  fold (C.insert_pre (insertion_context p description es) head entry);
  fold (pending p le head entry description es es []);
}

ghost
fn finish_indexed (#a: Type0) (p: L.ipayload a) (le: X.order a)
                  (head entry: L.lref) (description: a) (es: X.entries a)
                  (#front #back: X.entries a)
  requires L.is_list_ring_ix p head 1.0R (front @ ((entry, description) :: back)) **
    pending p le head entry description es front back **
    pure (X.total_preorder le /\ X.sorted le es)
  ensures post p le head entry description es
{
  unfold (pending p le head entry description es front back);
  rewrite (L.is_list_ring_ix p head 1.0R (front @ ((entry, description) :: back)))
    as (L.is_list_ring_ix p head 1.0R (X.insert le entry description es));
  X.insert_preserves_sorted le entry description es;
  fold (post p le head entry description es);
}

ghost
fn finish (#a: Type0) (p: L.ipayload a) (le: X.order a)
          (head entry: L.lref) (description: a) (es: X.entries a)
          (#front #back: X.entries a)
  requires C.insert_after_post (cut_context p head description front back) entry **
    pending p le head entry description es front back **
    pure (X.total_preorder le /\ X.sorted le es)
  ensures post p le head entry description es
{
  unfold (C.insert_after_post (cut_context p head description front back) entry);
  finish_indexed p le head entry description es;
}

ghost
fn finish_tail (#a: Type0) (p: L.ipayload a) (le: X.order a)
               (head entry: L.lref) (description: a) (es: X.entries a)
  requires C.insert_tail_post (insertion_context p description es) head entry **
    pending p le head entry description es es [] **
    pure (X.total_preorder le /\ X.sorted le es)
  ensures post p le head entry description es
{
  unfold (C.insert_tail_post (insertion_context p description es) head entry);
  finish_indexed p le head entry description es;
}

ghost
fn head_open (#a: Type0) (p: L.ipayload a) (le: X.order a)
             (head pos entry: L.lref) (description: a) (es: X.entries a)
  requires ready p le head pos entry description es
  ensures exists* (hv: N.struct_list_node).
    R.pts_to head hv ** pure (L.lnext hv == L.first_or head es) **
    T.trade (R.pts_to head hv) (ready p le head pos entry description es)
{
  unfold (ready p le head pos entry description es);
  with front back. assert (L.is_list_ring_ix p head 1.0R (front @ back));
  X.head_open p head (front @ back);
  with hv. assert (R.pts_to head hv);
  intro (T.trade (R.pts_to head hv) (ready p le head pos entry description es))
    #(X.head_rest p head (front @ back) hv)
  fn _ {
    X.head_close p head (front @ back);
    fold (ready p le head pos entry description es);
  };
}

ghost
fn head_close (#a: Type0) (p: L.ipayload a) (le: X.order a)
              (head pos entry: L.lref) (description: a) (es: X.entries a)
              (#hv: N.struct_list_node)
  requires R.pts_to head hv **
    T.trade (R.pts_to head hv) (ready p le head pos entry description es)
  ensures ready p le head pos entry description es
{
  T.elim_trade (R.pts_to head hv) (ready p le head pos entry description es);
}

ghost
fn prepare_head (#a: Type0) (p: L.ipayload a) (le: X.order a)
                (head pos entry: L.lref) (description: a) (es: X.entries a)
  requires ready p le head pos entry description es **
    R.pts_to_uninit entry ** p entry description **
    pure (pos == L.first_or head es) ** pure (pos =!= head)
  ensures C.insert_pre (insertion_context p description es) head entry **
    pending p le head entry description es [] es
{
  unfold (ready p le head pos entry description es);
  with front back. assert (L.is_list_ring_ix p head 1.0R (front @ back));
  X.ring_front_empty p head front back;
  rewrite (L.is_list_ring_ix p head 1.0R (front @ back))
    as (L.is_list_ring_ix p head 1.0R es);
  C.prepare_ring (insertion_context p description es).model head;
  fold (C.insert_pre (insertion_context p description es) head entry);
  fold (pending p le head entry description es [] es);
}

ghost
fn finish_head (#a: Type0) (p: L.ipayload a) (le: X.order a)
               (head entry: L.lref) (description: a) (es: X.entries a)
  requires C.insert_head_post (insertion_context p description es) head entry **
    pending p le head entry description es [] es **
    pure (X.total_preorder le /\ X.sorted le es)
  ensures post p le head entry description es
{
  unfold (C.insert_head_post (insertion_context p description es) head entry);
  finish_indexed p le head entry description es;
}

let after (#a: Type0) (p: L.ipayload a) (le: X.order a)
          (head prev entry: L.lref) (description: a) (es: X.entries a) : slprop =
  exists* (front back: X.entries a).
    L.is_list_ring_ix p head 1.0R (front @ back) **
    pure (prev == L.last_or head front) **
    pure (X.insert le entry description es == front @ ((entry, description) :: back))

ghost
fn position_open (#a: Type0) (p: L.ipayload a) (le: X.order a)
                 (head pos entry: L.lref) (description: a) (es: X.entries a)
  requires ready p le head pos entry description es ** pure (pos =!= head)
  ensures exists* (v: N.struct_list_node).
    R.pts_to pos v **
    T.trade (R.pts_to pos v) (after p le head (L.lprev v) entry description es)
{
  unfold (ready p le head pos entry description es);
  with front back. assert (L.is_list_ring_ix p head 1.0R (front @ back));
  X.split_open p head front back;
  with cur. assert (X.split p head cur front back);
  let e = Cons?.hd back;
  let rest = Cons?.tl back;
  rewrite (X.split p head cur front back) as (X.split p head pos front (e :: rest));
  X.cursor_expose p head pos front e rest;
  with v. assert (R.pts_to pos v);
  unfold (X.cursor_rest p head pos front (snd e) rest v);
  fold (X.cursor_rest p head pos front (snd e) rest v);
  intro (T.trade (R.pts_to pos v) (after p le head (L.lprev v) entry description es))
    #(p pos (snd e) ** X.cursor_rest p head pos front (snd e) rest v)
  fn _ {
    X.cursor_restore p head pos front (snd e) rest;
    X.split_close p head pos front ((pos, snd e) :: rest);
    fold (after p le head (L.lprev v) entry description es);
  };
}

ghost
fn position_close (#a: Type0) (p: L.ipayload a) (le: X.order a)
                  (head pos prev entry: L.lref) (description: a) (es: X.entries a)
                  (#v: N.struct_list_node)
  requires R.pts_to pos v **
    T.trade (R.pts_to pos v) (after p le head (L.lprev v) entry description es) **
    pure (prev == L.lprev v)
  ensures after p le head prev entry description es
{
  T.elim_trade (R.pts_to pos v) (after p le head (L.lprev v) entry description es);
  rewrite (after p le head (L.lprev v) entry description es)
    as (after p le head prev entry description es);
}

ghost
fn prepare_after (#a: Type0) (p: L.ipayload a) (le: X.order a)
                 (head prev entry: L.lref) (description: a) (es: X.entries a)
  requires after p le head prev entry description es **
    R.pts_to_uninit entry ** p entry description
  ensures exists* (front back: X.entries a).
    C.insert_after_pre (cut_context p head description front back) prev entry **
    pending p le head entry description es front back
{
  unfold (after p le head prev entry description es);
  with front back. assert (L.is_list_ring_ix p head 1.0R (front @ back));
  prepare_cut p le head entry description es front back;
  rewrite (C.insert_after_pre (cut_context p head description front back)
    (L.last_or head front) entry)
    as (C.insert_after_pre (cut_context p head description front back) prev entry);
}
