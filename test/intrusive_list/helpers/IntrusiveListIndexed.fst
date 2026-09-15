module IntrusiveListIndexed
open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module R = Pulse.Lib.Reference
module N = Struct_list_node
module L = IntrusiveList

(* Cursors preserve ordered descriptions without interpreting their payloads. *)
unfold let entry (a: Type0) = L.lref & a
unfold let entries (a: Type0) = list (entry a)
unfold let matcher (a: Type0) = L.lref -> a -> GTot bool
unfold let order (a: Type0) = a -> a -> GTot bool

let total_preorder (#a: Type0) (le: order a) : prop =
  (forall x. le x x) /\
  (forall x y z. le x y /\ le y z ==> le x z) /\
  (forall x y. le x y \/ le y x)

let rec first_match_entry (#a: Type0) (m: matcher a) (es: entries a)
  : GTot (option (entry a)) (decreases es)
  = match es with
    | [] -> None
    | e :: rest -> if m (fst e) (snd e) then Some e else first_match_entry m rest

let first_match (#a: Type0) (m: matcher a) (es: entries a) : GTot L.lref =
  match first_match_entry m es with | None -> null | Some e -> fst e

let rec no_match (#a: Type0) (m: matcher a) (es: entries a)
  : GTot prop (decreases es)
  = match es with
    | [] -> True
    | e :: rest -> not (m (fst e) (snd e)) /\ no_match m rest

let rec without (#a: Type0) (m: matcher a) (es: entries a)
  : GTot (entries a) (decreases es)
  = match es with
    | [] -> []
    | e :: rest -> if m (fst e) (snd e) then without m rest else e :: without m rest

let rec matching (#a: Type0) (m: matcher a) (es: entries a)
  : GTot (entries a) (decreases es)
  = match es with
    | [] -> []
    | e :: rest -> if m (fst e) (snd e) then e :: matching m rest else matching m rest

let rec sorted (#a: Type0) (le: order a) (es: entries a)
  : GTot prop (decreases es)
  = match es with
    | [] -> True
    | [_] -> True
    | e :: f :: rest -> le (snd e) (snd f) /\ sorted le (f :: rest)

(* Existing equivalent descriptions precede the inserted entry. *)
let rec insert (#a: Type0) (le: order a) (node: L.lref) (description: a)
               (es: entries a)
  : GTot (entries a) (decreases es)
  = match es with
    | [] -> [(node, description)]
    | e :: rest ->
      if le (snd e) description
      then e :: insert le node description rest
      else (node, description) :: es

let rec first_match_skip (#a: Type0) (m: matcher a) (front back: entries a)
  : Lemma
    (requires no_match m front)
    (ensures first_match_entry m (front @ back) == first_match_entry m back /\
      first_match m (front @ back) == first_match m back)
    (decreases front)
  = match front with | [] -> () | _ :: rest -> first_match_skip m rest back

let rec no_match_snoc (#a: Type0) (m: matcher a) (front: entries a)
                     (node: L.lref) (description: a)
  : Lemma
    (requires no_match m front /\ not (m node description))
    (ensures no_match m (front @ [(node, description)]))
    (decreases front)
  = match front with
    | [] -> ()
    | _ :: rest -> no_match_snoc m rest node description

let rec without_append (#a: Type0) (m: matcher a) (front back: entries a)
  : Lemma (without m (front @ back) == without m front @ without m back)
    (decreases front)
  = match front with | [] -> () | _ :: rest -> without_append m rest back

let rec matching_append (#a: Type0) (m: matcher a) (front back: entries a)
  : Lemma (matching m (front @ back) == matching m front @ matching m back)
    (decreases front)
  = match front with | [] -> () | _ :: rest -> matching_append m rest back

let rec filtered_no_match (#a: Type0) (m: matcher a) (es: entries a)
  : Lemma (no_match m (without m es)) (decreases es)
  = match es with | [] -> () | _ :: rest -> filtered_no_match m rest

let rec insert_preserves_sorted (#a: Type0) (le: order a)
                                (node: L.lref) (description: a) (es: entries a)
  : Lemma
    (requires total_preorder le /\ sorted le es)
    (ensures sorted le (insert le node description es))
    (decreases es)
  = match es with
    | [] -> ()
    | [_] -> ()
    | _ :: rest -> insert_preserves_sorted le node description rest

let rec detached (#a: Type0) (p: L.ipayload a) (es: entries a)
  : Tot slprop (decreases es)
  = match es with
    | [] -> emp
    | e :: rest ->
      (exists* (v: N.struct_list_node). R.pts_to (fst e) v) **
      p (fst e) (snd e) ** detached p rest

ghost
fn rec detached_snoc (#a: Type0) (p: L.ipayload a) (es: entries a)
                     (node: L.lref) (description: a) (#v: N.struct_list_node)
  requires detached p es ** R.pts_to node v ** p node description
  ensures detached p (es @ [(node, description)])
  decreases es
{
  match es {
    Nil -> {
      unfold (detached p es);
      fold (detached p []);
      fold (detached p [(node, description)]);
    }
    Cons e rest -> {
      unfold (detached p es);
      detached_snoc p rest node description;
      fold (detached p (e :: (rest @ [(node, description)])));
      rewrite (detached p (e :: (rest @ [(node, description)])))
        as (detached p (es @ [(node, description)]));
    }
  }
}

ghost
fn ops_open (#a: Type0) (p: L.ipayload a) (head: L.lref) (es: entries a)
  requires L.is_list_ring_ix p head 1.0R es
  ensures L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of es) **
    L.ipayload_of p es
{
  L.ring_ix_open p head 1.0R es;
}

ghost
fn ops_close (#a: Type0) (p: L.ipayload a) (head: L.lref) (es: entries a)
  requires L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of es) **
    L.ipayload_of p es
  ensures L.is_list_ring_ix p head 1.0R es
{
  L.ring_ix_close p head 1.0R es;
}

ghost
fn ops_open_at (#a: Type0) (p: L.ipayload a) (head: L.lref)
               (front: entries a) (e: entry a) (back: entries a)
  requires L.is_list_ring_ix p head 1.0R (front @ (e :: back))
  ensures L.is_list_ring_with L.emp_pl head 1.0R
      (L.cells_of front @ (fst e :: L.cells_of back)) **
    L.ipayload_of p (front @ (e :: back))
{
  rewrite (L.is_list_ring_ix p head 1.0R (front @ (e :: back)))
    as (L.is_list_ring_ix p head 1.0R (front @ ((fst e, snd e) :: back)));
  L.ring_ix_open_at p head 1.0R front back (fst e) (snd e);
  rewrite (L.ipayload_of p (front @ ((fst e, snd e) :: back)))
    as (L.ipayload_of p (front @ (e :: back)));
}

ghost
fn ops_close_insert (#a: Type0) (p: L.ipayload a) (head: L.lref)
                    (front back: entries a) (node: L.lref) (description: a)
  requires L.is_list_ring_with L.emp_pl head 1.0R
      (L.cells_of front @ (node :: L.cells_of back)) **
    L.ipayload_of p (front @ ((node, description) :: back))
  ensures L.is_list_ring_ix p head 1.0R (front @ ((node, description) :: back))
{
  L.ring_ix_close_at p head 1.0R front back node description;
}

ghost
fn ops_close_remove (#a: Type0) (p: L.ipayload a) (head: L.lref)
                    (front back: entries a)
  requires L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of front @ L.cells_of back) **
    L.ipayload_of p (front @ back)
  ensures L.is_list_ring_ix p head 1.0R (front @ back)
{
  L.ring_ix_close_cat p head 1.0R front back;
}

let head_rest (#a: Type0) (p: L.ipayload a) (head: L.lref) (es: entries a)
              (hv: N.struct_list_node) : slprop =
  L.is_list_seg head (L.lnext hv) head 1.0R (L.cells_of es) **
  L.ipayload_of p es **
  pure (L.lprev hv == L.last_or head (L.cells_of es))

ghost
fn head_open (#a: Type0) (p: L.ipayload a) (head: L.lref) (es: entries a)
  requires L.is_list_ring_ix p head 1.0R es
  ensures exists* (hv: N.struct_list_node).
    R.pts_to head hv ** head_rest p head es hv **
    pure (L.lnext hv == L.first_or head (L.cells_of es)) **
    pure (L.lprev hv == L.last_or head (L.cells_of es)) **
    pure ((L.lnext hv == head) <==> (es == []))
{
  L.ring_ix_out p head 1.0R es;
  L.ring_open_full L.no_payload head;
  with hv. assert (R.pts_to head hv);
  L.cells_of_nil_iff es;
  fold (head_rest p head es hv);
}

ghost
fn head_close (#a: Type0) (p: L.ipayload a) (head: L.lref) (es: entries a)
              (#hv: N.struct_list_node)
  requires R.pts_to head hv ** head_rest p head es hv
  ensures L.is_list_ring_ix p head 1.0R es
{
  unfold (head_rest p head es hv);
  L.ring_close L.no_payload head;
  L.ring_ix_in p head 1.0R es;
}

let split (#a: Type0) (p: L.ipayload a) (head pos: L.lref)
          (front back: entries a) : slprop =
  L.is_list_split head 1.0R (L.last_or head (L.cells_of front)) pos
    (L.cells_of front) (L.cells_of back) **
  L.ipayload_of p (front @ back)

ghost
fn split_open (#a: Type0) (p: L.ipayload a) (head: L.lref) (front back: entries a)
  requires L.is_list_ring_ix p head 1.0R (front @ back)
  ensures exists* (pos: L.lref).
    split p head pos front back **
    pure (pos == L.first_or head (L.cells_of back)) **
    pure ((pos == head) <==> (back == []))
{
  L.ring_ix_out p head 1.0R (front @ back);
  L.cells_of_append front back;
  rewrite (L.is_list_ring head 1.0R (L.cells_of (front @ back)))
    as (L.is_list_ring head 1.0R (L.cells_of front @ L.cells_of back));
  L.split_open L.no_payload head (L.cells_of front) (L.cells_of back);
  with pos. assert (L.is_list_split head 1.0R (L.last_or head (L.cells_of front))
    pos (L.cells_of front) (L.cells_of back));
  L.split_cur_ne L.no_payload head (L.last_or head (L.cells_of front)) pos
    (L.cells_of front) (L.cells_of back);
  unfold (L.is_list_split_with L.no_payload head 1.0R
    (L.last_or head (L.cells_of front)) pos (L.cells_of front) (L.cells_of back));
  L.seg_first L.no_payload (L.last_or head (L.cells_of front)) pos head;
  fold (L.is_list_split_with L.no_payload head 1.0R
    (L.last_or head (L.cells_of front)) pos (L.cells_of front) (L.cells_of back));
  L.cells_of_nil_iff back;
  fold (split p head pos front back);
}

ghost
fn split_close (#a: Type0) (p: L.ipayload a) (head pos: L.lref)
               (front back: entries a)
  requires split p head pos front back
  ensures L.is_list_ring_ix p head 1.0R (front @ back)
{
  unfold (split p head pos front back);
  L.split_close L.no_payload head (L.last_or head (L.cells_of front)) pos
    (L.cells_of front) (L.cells_of back);
  L.cells_of_append front back;
  rewrite (L.is_list_ring head 1.0R (L.cells_of front @ L.cells_of back))
    as (L.is_list_ring head 1.0R (L.cells_of (front @ back)));
  L.ring_ix_in p head 1.0R (front @ back);
}

ghost
fn split_facts (#a: Type0) (p: L.ipayload a) (head pos: L.lref)
               (front back: entries a)
  requires split p head pos front back
  ensures split p head pos front back **
    pure (pos == L.first_or head (L.cells_of back)) **
    pure ((pos == head) <==> (back == []))
{
  unfold (split p head pos front back);
  L.split_cur_ne L.no_payload head (L.last_or head (L.cells_of front)) pos
    (L.cells_of front) (L.cells_of back);
  unfold (L.is_list_split_with L.no_payload head 1.0R
    (L.last_or head (L.cells_of front)) pos (L.cells_of front) (L.cells_of back));
  L.seg_first L.no_payload (L.last_or head (L.cells_of front)) pos head;
  fold (L.is_list_split_with L.no_payload head 1.0R
    (L.last_or head (L.cells_of front)) pos (L.cells_of front) (L.cells_of back));
  L.cells_of_nil_iff back;
  fold (split p head pos front back);
}

ghost
fn cursor_start (#a: Type0) (p: L.ipayload a) (head pos: L.lref) (es: entries a)
                (#hv: N.struct_list_node)
  requires R.pts_to head hv ** head_rest p head es hv ** pure (pos == L.lnext hv)
  ensures split p head pos [] es
{
  unfold (head_rest p head es hv);
  L.split_open_front_nil L.no_payload head (L.cells_of es) pos;
  rewrite (L.is_list_split head 1.0R head pos [] (L.cells_of es))
    as (L.is_list_split head 1.0R (L.last_or head (L.cells_of #a [])) pos
      (L.cells_of #a []) (L.cells_of es));
  rewrite (L.ipayload_of p es) as (L.ipayload_of p ([] @ es));
  fold (split p head pos [] es);
}

(* The exposed entry's payload is outside this predicate; all others remain owned. *)
let cursor_rest (#a: Type0) (p: L.ipayload a) (head pos: L.lref)
                (front: entries a) (description: a) (back: entries a)
                (v: N.struct_list_node) : slprop =
  L.iter_rest L.no_payload head (L.last_or head (L.cells_of front)) pos
    (L.cells_of front) pos (L.cells_of back) (L.lnext v) **
  L.ipayload_of p front ** L.ipayload_of p back **
  pure (L.lprev v == L.last_or head (L.cells_of front))

ghost
fn cursor_expose (#a: Type0) (p: L.ipayload a) (head pos: L.lref)
                 (front: entries a) (e: entry a) (back: entries a)
  requires split p head pos front (e :: back)
  ensures exists* (v: N.struct_list_node).
    R.pts_to pos v ** p pos (snd e) **
    cursor_rest p head pos front (snd e) back v **
    pure (pos == fst e) ** pure (pos =!= head) **
    pure (L.lnext v == L.first_or head (L.cells_of back)) **
    pure ((L.lnext v == head) <==> (back == []))
{
  unfold (split p head pos front (e :: back));
  rewrite (L.is_list_split head 1.0R (L.last_or head (L.cells_of front)) pos
      (L.cells_of front) (L.cells_of (e :: back)))
    as (L.is_list_split head 1.0R (L.last_or head (L.cells_of front)) pos
      (L.cells_of front) (fst e :: L.cells_of back));
  L.iter_expose L.no_payload head (L.last_or head (L.cells_of front)) pos
    (L.cells_of front) (fst e) (L.cells_of back);
  with v. assert (R.pts_to pos v);
  L.ipayload_of_split p front (e :: back);
  unfold (L.ipayload_of p (e :: back));
  rewrite (p (fst e) (snd e)) as (p pos (snd e));
  rewrite (L.iter_rest L.no_payload head (L.last_or head (L.cells_of front)) pos
      (L.cells_of front) (fst e) (L.cells_of back) (L.lnext v))
    as (L.iter_rest L.no_payload head (L.last_or head (L.cells_of front)) pos
      (L.cells_of front) pos (L.cells_of back) (L.lnext v));
  unfold (L.iter_rest L.no_payload head (L.last_or head (L.cells_of front)) pos
    (L.cells_of front) pos (L.cells_of back) (L.lnext v));
  L.seg_first L.no_payload pos (L.lnext v) head;
  L.seg_cur_ne L.no_payload pos (L.lnext v) head;
  L.cells_of_nil_iff back;
  fold (L.iter_rest L.no_payload head (L.last_or head (L.cells_of front)) pos
    (L.cells_of front) pos (L.cells_of back) (L.lnext v));
  fold (cursor_rest p head pos front (snd e) back v);
}

ghost
fn cursor_restore (#a: Type0) (p: L.ipayload a) (head pos: L.lref)
                  (front: entries a) (description: a) (back: entries a)
                  (#v: N.struct_list_node)
  requires R.pts_to pos v ** p pos description **
    cursor_rest p head pos front description back v
  ensures split p head pos front ((pos, description) :: back)
{
  unfold (cursor_rest p head pos front description back v);
  L.iter_unexpose L.no_payload head (L.last_or head (L.cells_of front)) pos
    (L.cells_of front) pos (L.cells_of back);
  L.ipayload_of_cons_in p pos description back;
  L.ipayload_of_join p front ((pos, description) :: back);
  rewrite (L.is_list_split head 1.0R (L.last_or head (L.cells_of front)) pos
      (L.cells_of front) (pos :: L.cells_of back))
    as (L.is_list_split head 1.0R (L.last_or head (L.cells_of front)) pos
      (L.cells_of front) (L.cells_of ((pos, description) :: back)));
  fold (split p head pos front ((pos, description) :: back));
}

ghost
fn cursor_advance (#a: Type0) (p: L.ipayload a) (head pos: L.lref)
                  (front: entries a) (description: a) (back: entries a)
                  (#v: N.struct_list_node)
  requires R.pts_to pos v ** p pos description **
    cursor_rest p head pos front description back v
  ensures split p head (L.lnext v) (front @ [(pos, description)]) back
{
  unfold (cursor_rest p head pos front description back v);
  L.iter_advance L.no_payload head (L.last_or head (L.cells_of front)) pos
    (L.cells_of front) pos (L.cells_of back);
  L.ipayload_of_single_in p pos description;
  L.ipayload_of_join p front [(pos, description)];
  L.ipayload_of_join p (front @ [(pos, description)]) back;
  L.cells_of_append front [(pos, description)];
  L.last_or_snoc head (L.cells_of front) pos;
  rewrite (L.is_list_split head 1.0R pos (L.lnext v) (L.cells_of front @ [pos])
      (L.cells_of back))
    as (L.is_list_split head 1.0R
      (L.last_or head (L.cells_of (front @ [(pos, description)]))) (L.lnext v)
      (L.cells_of (front @ [(pos, description)])) (L.cells_of back));
  fold (split p head (L.lnext v) (front @ [(pos, description)]) back);
}
