module IntrusiveListInsert
open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module R = Pulse.Lib.Reference
module N = Struct_list_node
module L = IntrusiveList
module X = IntrusiveListIndexed
module T = Pulse.Lib.Trade

[@@pulse_intro]
ghost
fn singleton_out (#pl: erased L.payload) (node: L.lref)
  requires L.payload_of (reveal pl) [node]
  ensures (reveal pl) node
{
  L.payload_of_single_out (reveal pl) node;
}

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
    pure (pos == L.first_or head (L.cells_of back)) **
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
  L.ipayload_of p (front @ ((entry, description) :: back)) **
  pure (X.insert le entry description es == front @ ((entry, description) :: back))

ghost
fn prepare_cut (#a: Type0) (p: L.ipayload a) (le: X.order a)
               (head entry: L.lref) (description: a) (es: X.entries a)
               (front back: X.entries a)
  requires L.is_list_ring_ix p head 1.0R (front @ back) ** p entry description **
    pure (X.insert le entry description es == front @ ((entry, description) :: back))
  ensures L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of front @ L.cells_of back) **
    L.payload_of L.emp_pl [entry] **
    pending p le head entry description es front back
{
  X.ops_open p head (front @ back);
  L.cells_of_append front back;
  rewrite (L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of (front @ back)))
    as (L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of front @ L.cells_of back));
  L.ipayload_of_insert p front back entry description;
  L.epl_single_in entry;
  fold (pending p le head entry description es front back);
}

ghost
fn prepare_tail (#a: Type0) (p: L.ipayload a) (le: X.order a)
                (head pos entry: L.lref) (description: a) (es: X.entries a)
  requires ready p le head pos entry description es ** p entry description **
    pure (pos == head)
  ensures L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of es) **
    L.payload_of L.emp_pl [entry] **
    pending p le head entry description es es []
{
  unfold (ready p le head pos entry description es);
  with front back. assert (L.is_list_ring_ix p head 1.0R (front @ back));
  FStar.List.Tot.Properties.append_l_nil front;
  rewrite (L.is_list_ring_ix p head 1.0R (front @ back))
    as (L.is_list_ring_ix p head 1.0R (es @ []));
  prepare_cut p le head entry description es es [];
  FStar.List.Tot.Properties.append_l_nil (L.cells_of es);
  rewrite (L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of es @ L.cells_of #a []))
    as (L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of es));
}

ghost
fn finish (#a: Type0) (p: L.ipayload a) (le: X.order a)
          (head entry: L.lref) (description: a) (es: X.entries a)
          (#front #back: X.entries a)
  requires L.is_list_ring_with L.emp_pl head 1.0R
      (L.cells_of front @ (entry :: L.cells_of back)) **
    pending p le head entry description es front back **
    pure (X.total_preorder le /\ X.sorted le es)
  ensures post p le head entry description es
{
  unfold (pending p le head entry description es front back);
  X.ops_close_insert p head front back entry description;
  rewrite (L.is_list_ring_ix p head 1.0R (front @ ((entry, description) :: back)))
    as (L.is_list_ring_ix p head 1.0R (X.insert le entry description es));
  X.insert_preserves_sorted le entry description es;
  fold (post p le head entry description es);
}

ghost
fn finish_tail (#a: Type0) (p: L.ipayload a) (le: X.order a)
               (head entry: L.lref) (description: a) (es: X.entries a)
  requires L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of es @ [entry]) **
    pending p le head entry description es es [] **
    pure (X.total_preorder le /\ X.sorted le es)
  ensures post p le head entry description es
{
  rewrite (L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of es @ [entry]))
    as (L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of es @ (entry :: L.cells_of #a [])));
  finish p le head entry description es;
}

ghost
fn head_open (#a: Type0) (p: L.ipayload a) (le: X.order a)
             (head pos entry: L.lref) (description: a) (es: X.entries a)
  requires ready p le head pos entry description es
  ensures exists* (hv: N.struct_list_node).
    R.pts_to head hv ** pure (L.lnext hv == L.first_or head (L.cells_of es)) **
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
fn empty_cut (pl: L.payload) (prev start cut sent: L.lref) (cells: list L.lref)
  requires L.is_list_seg_s_with pl prev start cut sent 1.0R cells ** pure (start == cut)
  ensures L.is_list_seg_s_with pl prev start cut sent 1.0R cells ** pure (cells == [])
{
  match cells {
    Nil -> {}
    Cons x xs -> {
      unfold (L.is_list_seg_s_with pl prev start cut sent 1.0R cells);
      unreachable ();
    }
  }
}

ghost
fn prepare_head (#a: Type0) (p: L.ipayload a) (le: X.order a)
                (head pos entry: L.lref) (description: a) (es: X.entries a)
  requires ready p le head pos entry description es ** p entry description **
    pure (pos == L.first_or head (L.cells_of es)) ** pure (pos =!= head)
  ensures L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of es) **
    L.payload_of L.emp_pl [entry] ** pending p le head entry description es [] es
{
  unfold (ready p le head pos entry description es);
  with front back. assert (L.is_list_ring_ix p head 1.0R (front @ back));
  L.ring_ix_out p head 1.0R (front @ back);
  L.cells_of_append front back;
  rewrite (L.is_list_ring head 1.0R (L.cells_of (front @ back)))
    as (L.is_list_ring head 1.0R (L.cells_of front @ L.cells_of back));
  L.ring_open_full L.no_payload head;
  with hv. assert (R.pts_to head hv);
  L.seg_split L.no_payload head (L.lnext hv) head (L.cells_of front) (L.cells_of back);
  with cur. assert (L.is_list_seg_with L.no_payload
    (L.last_or head (L.cells_of front)) cur head 1.0R (L.cells_of back));
  L.seg_first L.no_payload (L.last_or head (L.cells_of front)) cur head;
  empty_cut L.no_payload head (L.lnext hv) cur head (L.cells_of front);
  L.cells_of_nil_iff front;
  L.seg_merge L.no_payload head (L.lnext hv) cur head (L.cells_of front) (L.cells_of back);
  L.ring_close L.no_payload head;
  rewrite (L.is_list_ring head 1.0R (L.cells_of front @ L.cells_of back))
    as (L.is_list_ring head 1.0R (L.cells_of (front @ back)));
  L.ring_ix_in p head 1.0R (front @ back);
  rewrite (L.is_list_ring_ix p head 1.0R (front @ back))
    as (L.is_list_ring_ix p head 1.0R ([] @ es));
  prepare_cut p le head entry description es [] es;
  rewrite (L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of #a [] @ L.cells_of es))
    as (L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of es));
}

ghost
fn finish_head (#a: Type0) (p: L.ipayload a) (le: X.order a)
               (head entry: L.lref) (description: a) (es: X.entries a)
  requires L.is_list_ring_with L.emp_pl head 1.0R (entry :: L.cells_of es) **
    pending p le head entry description es [] es **
    pure (X.total_preorder le /\ X.sorted le es)
  ensures post p le head entry description es
{
  rewrite (L.is_list_ring_with L.emp_pl head 1.0R (entry :: L.cells_of es))
    as (L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of #a [] @ (entry :: L.cells_of es)));
  finish p le head entry description es;
}

let after (#a: Type0) (p: L.ipayload a) (le: X.order a)
          (head prev entry: L.lref) (description: a) (es: X.entries a) : slprop =
  exists* (front back: X.entries a).
    L.is_list_ring_ix p head 1.0R (front @ back) **
    pure (prev == L.last_or head (L.cells_of front)) **
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
  requires after p le head prev entry description es ** p entry description
  ensures exists* (front back: X.entries a).
    L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of front @ L.cells_of back) **
    L.payload_of L.emp_pl [entry] ** pending p le head entry description es front back **
    pure (prev == L.last_or head (L.cells_of front))
{
  unfold (after p le head prev entry description es);
  with front back. assert (L.is_list_ring_ix p head 1.0R (front @ back));
  prepare_cut p le head entry description es front back;
}
