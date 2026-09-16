module IntrusiveListItems

(* Generic first-match traversal and ownership-returning pop. Concrete container
   recovery and field comparisons belong to the client-specific Example modules. *)

open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module R = Pulse.Lib.Reference
module N = Struct_list_node
module X = IntrusiveListIndexed
module C = IntrusiveListContext

let find_post (#a: Type0) (p: X.ipayload a) (m: X.matcher a)
              (head: X.lref) (es: X.entries a) (result: X.lref) : slprop =
  X.is_list_ring_ix p head 1.0R es ** pure (result == X.first_match m es)

let find_inv (#a: Type0) (p: X.ipayload a) (m: X.matcher a)
             (head pos: X.lref) (es: X.entries a) : slprop =
  exists* (front back: X.entries a).
    X.split p head pos front back **
    pure (front @ back == es) ** pure (X.no_match m front)

let find_mid (#a: Type0) (p: X.ipayload a) (m: X.matcher a)
             (head pos: X.lref) (es: X.entries a) (description: a)
             (v: N.struct_list_node) : slprop =
  exists* (front back: X.entries a).
    X.cursor_rest p head pos front description back v **
    pure (front @ ((pos, description) :: back) == es) **
    pure (X.no_match m front)

ghost
fn find_start (#a: Type0) (p: X.ipayload a) (m: X.matcher a)
              (head pos: X.lref) (es: X.entries a) (#hv: N.struct_list_node)
  requires R.pts_to head hv ** X.head_rest p head es hv ** pure (pos == X.lnext hv)
  ensures find_inv p m head pos es
{
  X.cursor_start p head pos es;
  fold (find_inv p m head pos es);
}

ghost
fn find_open (#a: Type0) (p: X.ipayload a) (m: X.matcher a)
             (head pos: X.lref) (es: X.entries a)
  requires find_inv p m head pos es ** pure (pos =!= head)
  ensures exists* (description: a) (v: N.struct_list_node).
    R.pts_to pos v ** p pos description ** find_mid p m head pos es description v
{
  unfold (find_inv p m head pos es);
  with front back. assert (X.split p head pos front back);
  X.split_facts p head pos front back;
  let e = Cons?.hd back;
  let rest = Cons?.tl back;
  rewrite (X.split p head pos front back) as (X.split p head pos front (e :: rest));
  X.cursor_expose p head pos front e rest;
  with v. assert (R.pts_to pos v);
  fold (find_mid p m head pos es (snd e) v);
}

ghost
fn find_found (#a: Type0) (p: X.ipayload a) (m: X.matcher a)
              (head pos: X.lref) (es: X.entries a) (description: a)
              (#v: N.struct_list_node)
  requires R.pts_to pos v ** p pos description ** find_mid p m head pos es description v **
    pure (m pos description)
  ensures X.is_list_ring_ix p head 1.0R es **
    pure (X.first_match_entry m es == Some (pos, description)) **
    pure (X.first_match m es == pos)
{
  unfold (find_mid p m head pos es description v);
  with front back. assert (X.cursor_rest p head pos front description back v);
  X.first_match_skip m front ((pos, description) :: back);
  X.cursor_restore p head pos front description back;
  X.split_close p head pos front ((pos, description) :: back);
  rewrite (X.is_list_ring_ix p head 1.0R (front @ ((pos, description) :: back)))
    as (X.is_list_ring_ix p head 1.0R es);
}

ghost
fn find_step (#a: Type0) (p: X.ipayload a) (m: X.matcher a)
             (head pos next: X.lref) (es: X.entries a) (description: a)
             (#v: N.struct_list_node)
  requires R.pts_to pos v ** p pos description ** find_mid p m head pos es description v **
    pure (not (m pos description)) ** pure (next == X.lnext v)
  ensures find_inv p m head next es
{
  unfold (find_mid p m head pos es description v);
  with front back. assert (X.cursor_rest p head pos front description back v);
  X.no_match_snoc m front pos description;
  X.cursor_advance p head pos front description back;
  FStar.List.Tot.Properties.append_assoc front [(pos, description)] back;
  rewrite (X.split p head (X.lnext v) (front @ [(pos, description)]) back)
    as (X.split p head next (front @ [(pos, description)]) back);
  fold (find_inv p m head next es);
}

ghost
fn find_end (#a: Type0) (p: X.ipayload a) (m: X.matcher a)
            (head pos: X.lref) (es: X.entries a)
  requires find_inv p m head pos es ** pure (pos == head)
  ensures X.is_list_ring_ix p head 1.0R es **
    pure (X.first_match_entry m es == None) ** pure (X.first_match m es == null)
{
  unfold (find_inv p m head pos es);
  with front back. assert (X.split p head pos front back);
  X.split_facts p head pos front back;
  X.first_match_skip m front back;
  X.split_close p head pos front back;
  rewrite (X.is_list_ring_ix p head 1.0R (front @ back))
    as (X.is_list_ring_ix p head 1.0R es);
}

let pop_post (#a: Type0) (p: X.ipayload a) (head: X.lref)
             (es: X.entries a) (result: X.lref) : slprop =
  match es with
  | [] -> X.is_list_ring_ix p head 1.0R [] ** pure (result == null)
  | e :: rest ->
    X.is_list_ring_ix p head 1.0R rest **
    (exists* (v: N.struct_list_node). R.pts_to (fst e) v) **
    p (fst e) (snd e) ** pure (result == fst e)

ghost
fn pop_empty (#a: Type0) (p: X.ipayload a) (head: X.lref) (es: X.entries a)
  requires X.is_list_ring_ix p head 1.0R es ** pure (es == [])
  ensures pop_post p head es null
{
  rewrite (X.is_list_ring_ix p head 1.0R es) as (X.is_list_ring_ix p head 1.0R []);
  fold (pop_post p head [] null);
  rewrite (pop_post p head [] null) as (pop_post p head es null);
}

ghost
fn pop_finish (#a: Type0) (p: X.ipayload a) (head result: X.lref) (es: X.entries a)
  requires C.remove_head_post (C.make p es) head result
  ensures pop_post p head es result
{
  match es {
    Nil -> {
      rewrite (C.remove_head_post (C.make p es) head result) as (pure False);
      unreachable ();
    }
    Cons e rest -> {
      rewrite (C.remove_head_post (C.make p es) head result)
        as (X.is_list_ring_ix p head 1.0R rest **
          (exists* (next: X.lref). R.pts_to result (X.mklink next head)) **
          p result (snd e) ** pure (result == fst e));
      with next. assert (R.pts_to result (X.mklink next head));
      rewrite (R.pts_to result (X.mklink next head))
        as (R.pts_to (fst e) (X.mklink next head));
      rewrite (p result (snd e)) as (p (fst e) (snd e));
      fold (pop_post p head es result);
    }
  }
}
