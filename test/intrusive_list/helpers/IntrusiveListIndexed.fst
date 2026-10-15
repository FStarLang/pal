module IntrusiveListIndexed

(* Canonical indexed ownership: each member owns its links and P node description;
   the sentinel owns only its links. Structural proofs never inspect P. *)

open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module R = IntrusiveListNodeRef
module N = Struct_list_node

unfold let lref = R.ref N.struct_list_node

(* The node points-to under whatever name the memory model gives it. The C
   sources name this rather than the model's own predicate, so that one set of
   annotations serves both models. *)
unfold let lpts_to (r: lref) (v: N.struct_list_node) : slprop = R.pts_to r v
unfold let lpts_to_uninit (r: lref) : slprop = R.pts_to_uninit r

unfold let lnext (v: N.struct_list_node) : lref = v.N.fld_next
unfold let lprev (v: N.struct_list_node) : lref = v.N.fld_prev
unfold let mklink (next prev: lref) : N.struct_list_node = {
  N.fld_next = next;
  N.fld_prev = prev;
}

unfold let ipayload (a: Type0) = lref -> a -> slprop
unfold let no_payload (#a: Type0) : ipayload a = fun _ _ -> emp
unfold let emp_pl (#a: Type0) : ipayload a = no_payload

(* Cursors preserve ordered descriptions without interpreting their payloads. *)
unfold let entry (a: Type0) = lref & a
unfold let entries (a: Type0) = list (entry a)
unfold let matcher (a: Type0) = lref -> a -> GTot bool
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

let first_match (#a: Type0) (m: matcher a) (es: entries a) : GTot lref =
  match first_match_entry m es with | None -> R.null | Some e -> fst e

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
let rec insert (#a: Type0) (le: order a) (node: lref) (description: a)
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
                     (node: lref) (description: a)
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
                                (node: lref) (description: a) (es: entries a)
  : Lemma
    (requires total_preorder le /\ sorted le es)
    (ensures sorted le (insert le node description es))
    (decreases es)
  = match es with
    | [] -> ()
    | [_] -> ()
    | _ :: rest -> insert_preserves_sorted le node description rest

let rec detached (#a: Type0) (p: ipayload a) (es: entries a)
  : Tot slprop (decreases es)
  = match es with
    | [] -> emp
    | e :: rest ->
      (exists* (v: N.struct_list_node). R.pts_to (fst e) v) **
      p (fst e) (snd e) ** detached p rest

ghost
fn rec detached_snoc (#a: Type0) (p: ipayload a) (es: entries a)
                     (node: lref) (description: a) (#v: N.struct_list_node)
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

let first_or (#a: Type0) (d: lref) (es: entries a) : lref =
  match es with | [] -> d | e :: _ -> fst e

let rec last_or (#a: Type0) (d: lref) (es: entries a)
  : Tot lref (decreases es) =
  match es with | [] -> d | e :: rest -> last_or (fst e) rest

let rec cells_of (#a: Type0) (es: entries a) : Tot (list lref) (decreases es) =
  match es with | [] -> [] | e :: rest -> fst e :: cells_of rest

let rec cells_of_append (#a: Type0) (front back: entries a)
  : Lemma (cells_of (front @ back) == cells_of front @ cells_of back)
    (decreases front) =
  match front with | [] -> () | _ :: rest -> cells_of_append rest back

let cells_of_nil_iff (#a: Type0) (es: entries a)
  : Lemma ((cells_of es == []) <==> (es == [])) =
  match es with | [] -> () | _ :: _ -> ()

let rec last_or_append (#a: Type0) (d: lref) (front back: entries a)
  : Lemma (last_or d (front @ back) == last_or (last_or d front) back)
    (decreases front) =
  match front with | [] -> () | e :: rest -> last_or_append (fst e) rest back

let last_or_cons (#a: Type0) (d: lref) (e: entry a) (es: entries a)
  : Lemma (last_or d (e :: es) == last_or (fst e) es) = ()

let last_or_snoc (#a: Type0) (d: lref) (es: entries a) (e: entry a)
  : Lemma (last_or d (es @ [e]) == fst e) =
  last_or_append d es [e]

(* The endpoint is excluded. Descriptions travel with their node ownership. *)
let rec is_list_seg_ix (#a: Type0) (pl: ipayload a)
    (prev cur endl: lref) (p: perm) (es: entries a)
  : Tot slprop (decreases es) =
  match es with
  | [] -> pure (cur == endl)
  | e :: rest ->
    pure (cur == fst e) ** pure (cur =!= endl) **
    (exists* (v: N.struct_list_node).
      R.pts_to cur #p v ** pl cur (snd e) **
      pure (lprev v == prev) **
      is_list_seg_ix pl cur (lnext v) endl p rest)

(* The sentinel has links but no member description or payload. *)
let is_list_ring_ix (#a: Type0) (pl: ipayload a)
    ([@@@mkey] head: lref) (p: perm) (es: entries a) : slprop =
  exists* (hv: N.struct_list_node).
    R.pts_to head #p hv **
    is_list_seg_ix pl head (lnext hv) head p es **
    pure (lprev hv == last_or head es)

ghost
fn seg_nil_intro (#a: Type0) (pl: ipayload a) (prev cur endl: lref) (p: perm)
  requires pure (cur == endl)
  ensures is_list_seg_ix pl prev cur endl p []
{
  fold (is_list_seg_ix pl prev cur endl p []);
}

ghost
fn seg_nil_elim (#a: Type0) (pl: ipayload a) (prev cur endl: lref) (p: perm)
  requires is_list_seg_ix pl prev cur endl p []
  ensures pure (cur == endl)
{
  unfold (is_list_seg_ix pl prev cur endl p []);
}

ghost
fn seg_cons_intro (#a: Type0) (pl: ipayload a) (prev cur endl: lref)
                  (p: perm) (e: entry a) (rest: entries a) (#v: N.struct_list_node)
  requires R.pts_to cur #p v ** pl cur (snd e) **
    pure (cur == fst e /\ cur =!= endl /\ lprev v == prev) **
    is_list_seg_ix pl cur (lnext v) endl p rest
  ensures is_list_seg_ix pl prev cur endl p (e :: rest)
{
  fold (is_list_seg_ix pl prev cur endl p (e :: rest));
}

ghost
fn seg_cons_elim (#a: Type0) (pl: ipayload a) (prev cur endl: lref)
                 (p: perm) (e: entry a) (rest: entries a)
  requires is_list_seg_ix pl prev cur endl p (e :: rest)
  ensures exists* (v: N.struct_list_node).
    R.pts_to cur #p v ** pl cur (snd e) **
    pure (cur == fst e /\ cur =!= endl /\ lprev v == prev) **
    is_list_seg_ix pl cur (lnext v) endl p rest
{
  unfold (is_list_seg_ix pl prev cur endl p (e :: rest));
}

ghost
fn seg_first (#a: Type0) (pl: ipayload a) (prev cur endl: lref)
             (#p: perm) (#es: entries a)
  requires is_list_seg_ix pl prev cur endl p es
  ensures is_list_seg_ix pl prev cur endl p es **
    pure (cur == first_or endl es) ** pure ((cur == endl) <==> (es == []))
{
  if (Nil? es) {
    rewrite (is_list_seg_ix pl prev cur endl p es) as (is_list_seg_ix pl prev cur endl p []);
    unfold (is_list_seg_ix pl prev cur endl p []);
    fold (is_list_seg_ix pl prev cur endl p []);
    rewrite (is_list_seg_ix pl prev cur endl p []) as (is_list_seg_ix pl prev cur endl p es);
  } else {
    let e = Cons?.hd es;
    let rest = Cons?.tl es;
    rewrite (is_list_seg_ix pl prev cur endl p es)
      as (is_list_seg_ix pl prev cur endl p (e :: rest));
    unfold (is_list_seg_ix pl prev cur endl p (e :: rest));
    fold (is_list_seg_ix pl prev cur endl p (e :: rest));
    rewrite (is_list_seg_ix pl prev cur endl p (e :: rest))
      as (is_list_seg_ix pl prev cur endl p es);
  }
}

ghost
fn rec seg_last_ne (#a: Type0) (pl: ipayload a) (prev cur endl: lref)
                   (#p: perm) (es: entries a)
  requires is_list_seg_ix pl prev cur endl p es
  ensures is_list_seg_ix pl prev cur endl p es **
    pure ((last_or endl es == endl) <==> (es == []))
  decreases es
{
  match es {
    Nil -> {
      unfold (is_list_seg_ix pl prev cur endl p []);
      fold (is_list_seg_ix pl prev cur endl p []);
    }
    Cons e rest -> {
      seg_cons_elim pl prev cur endl p e rest;
      with v. assert (R.pts_to cur #p v);
      seg_last_ne pl cur (lnext v) endl rest;
      seg_cons_intro pl prev cur endl p e rest;
    }
  }
}

ghost
fn ring_open (#a: Type0) (pl: ipayload a) (head: lref)
             (#p: perm) (#es: entries a)
  requires is_list_ring_ix pl head p es
  ensures exists* (hv: N.struct_list_node).
    R.pts_to head #p hv ** is_list_seg_ix pl head (lnext hv) head p es **
    pure (lprev hv == last_or head es /\ lnext hv == first_or head es) **
    pure ((lnext hv == head) <==> (es == [])) **
    pure ((lprev hv == head) <==> (es == []))
{
  unfold (is_list_ring_ix pl head p es);
  with hv. assert (R.pts_to head #p hv);
  seg_first pl head (lnext hv) head;
  seg_last_ne pl head (lnext hv) head es;
}

ghost
fn ring_close (#a: Type0) (pl: ipayload a) (head: lref)
              (#p: perm) (#es: entries a) (#hv: N.struct_list_node)
  requires R.pts_to head #p hv ** is_list_seg_ix pl head (lnext hv) head p es **
    pure (lprev hv == last_or head es)
  ensures is_list_ring_ix pl head p es
{
  fold (is_list_ring_ix pl head p es);
}

ghost
fn ring_intro_empty (#a: Type0) (pl: ipayload a) (head: lref)
                    (#p: perm) (#hv: N.struct_list_node)
  requires R.pts_to head #p hv ** pure (lnext hv == head /\ lprev hv == head)
  ensures is_list_ring_ix pl head p []
{
  seg_nil_intro pl head (lnext hv) head p;
  ring_close pl head;
}

ghost
fn ring_elim_empty (#a: Type0) (pl: ipayload a) (head: lref) (#p: perm)
  requires is_list_ring_ix pl head p []
  ensures exists* (hv: N.struct_list_node).
    R.pts_to head #p hv ** pure (lnext hv == head /\ lprev hv == head)
{
  ring_open pl head;
  with hv. assert (R.pts_to head #p hv);
  seg_nil_elim pl head (lnext hv) head p;
}

let rec ipayload_of (#a: Type0) (pl: ipayload a) (es: entries a)
  : Tot slprop (decreases es) =
  match es with
  | [] -> emp
  | e :: rest -> pl (fst e) (snd e) ** ipayload_of pl rest

ghost
fn rec ipayload_of_split (#a: Type0) (pl: ipayload a) (front back: entries a)
  requires ipayload_of pl (front @ back)
  ensures ipayload_of pl front ** ipayload_of pl back
  decreases front
{
  match front {
    Nil -> { fold (ipayload_of pl []); }
    Cons e rest -> {
      rewrite (ipayload_of pl (front @ back)) as (ipayload_of pl (e :: (rest @ back)));
      unfold (ipayload_of pl (e :: (rest @ back)));
      ipayload_of_split pl rest back;
      fold (ipayload_of pl (e :: rest));
    }
  }
}

ghost
fn rec ipayload_of_join (#a: Type0) (pl: ipayload a) (front back: entries a)
  requires ipayload_of pl front ** ipayload_of pl back
  ensures ipayload_of pl (front @ back)
  decreases front
{
  match front {
    Nil -> { unfold (ipayload_of pl []); }
    Cons e rest -> {
      unfold (ipayload_of pl (e :: rest));
      ipayload_of_join pl rest back;
      fold (ipayload_of pl (e :: (rest @ back)));
      rewrite (ipayload_of pl (e :: (rest @ back))) as (ipayload_of pl (front @ back));
    }
  }
}

ghost
fn rec seg_pl_out (#a: Type0) (pl: ipayload a) (prev cur endl: lref)
                  (p: perm) (es: entries a)
  requires is_list_seg_ix pl prev cur endl p es
  ensures is_list_seg_ix no_payload prev cur endl p es ** ipayload_of pl es
  decreases es
{
  match es {
    Nil -> {
      seg_nil_elim pl prev cur endl p;
      seg_nil_intro #a no_payload prev cur endl p;
      fold (ipayload_of pl []);
    }
    Cons e rest -> {
      seg_cons_elim pl prev cur endl p e rest;
      with v. assert (R.pts_to cur #p v);
      seg_pl_out pl cur (lnext v) endl p rest;
      seg_cons_intro no_payload prev cur endl p e rest;
      rewrite (pl cur (snd e)) as (pl (fst e) (snd e));
      fold (ipayload_of pl (e :: rest));
    }
  }
}

ghost
fn rec seg_pl_in (#a: Type0) (pl: ipayload a) (prev cur endl: lref)
                 (p: perm) (es: entries a)
  requires is_list_seg_ix no_payload prev cur endl p es ** ipayload_of pl es
  ensures is_list_seg_ix pl prev cur endl p es
  decreases es
{
  match es {
    Nil -> {
      seg_nil_elim no_payload prev cur endl p;
      unfold (ipayload_of pl []);
      seg_nil_intro pl prev cur endl p;
    }
    Cons e rest -> {
      seg_cons_elim no_payload prev cur endl p e rest;
      with v. assert (R.pts_to cur #p v);
      unfold (ipayload_of pl (e :: rest));
      seg_pl_in pl cur (lnext v) endl p rest;
      rewrite (pl (fst e) (snd e)) as (pl cur (snd e));
      seg_cons_intro pl prev cur endl p e rest;
    }
  }
}

ghost
fn ring_pl_out (#a: Type0) (pl: ipayload a) (head: lref) (p: perm) (es: entries a)
  requires is_list_ring_ix pl head p es
  ensures is_list_ring_ix no_payload head p es ** ipayload_of pl es
{
  ring_open pl head;
  with hv. assert (R.pts_to head #p hv);
  seg_pl_out pl head (lnext hv) head p es;
  ring_close no_payload head;
}

ghost
fn ring_pl_in (#a: Type0) (pl: ipayload a) (head: lref) (p: perm) (es: entries a)
  requires is_list_ring_ix no_payload head p es ** ipayload_of pl es
  ensures is_list_ring_ix pl head p es
{
  ring_open no_payload head;
  with hv. assert (R.pts_to head #p hv);
  seg_pl_in pl head (lnext hv) head p es;
  ring_close pl head;
}

(* A split prefix excludes both the cut and the original sentinel. *)
let rec is_list_seg_s_ix (#a: Type0) (pl: ipayload a)
    (prev cur endl sent: lref) (p: perm) (es: entries a)
  : Tot slprop (decreases es) =
  match es with
  | [] -> pure (cur == endl)
  | e :: rest ->
    pure (cur == fst e /\ cur =!= endl /\ cur =!= sent) **
    (exists* (v: N.struct_list_node).
      R.pts_to cur #p v ** pl cur (snd e) **
      pure (lprev v == prev) **
      is_list_seg_s_ix pl cur (lnext v) endl sent p rest)

ghost
(* Monomorphic under Palow: a points-to there says how the bytes are laid
   out, so it is per type, and every caller of this is at the node type. *)
fn refs_distinct (r1 r2: lref) (#v1 #v2: N.struct_list_node)
  requires R.pts_to r1 v1 ** R.pts_to r2 v2
  ensures R.pts_to r1 v1 ** R.pts_to r2 v2 ** pure (r1 =!= r2)
{
  let equal = FStar.IndefiniteDescription.strong_excluded_middle (r1 == r2);
  if equal {
    rewrite (R.pts_to r2 v2) as (R.pts_to r1 v2);
    R.gather r1;
    R.pts_to_perm_bound r1;
    unreachable ();
  }
}

ghost
fn seg_head_distinct (#a: Type0) (pl: ipayload a)
                     (start sent prev cur: lref) (es: entries a)
                     (#v: N.struct_list_node)
  requires R.pts_to start v ** is_list_seg_ix pl prev cur sent 1.0R es **
    pure (start =!= sent)
  ensures R.pts_to start v ** is_list_seg_ix pl prev cur sent 1.0R es **
    pure (start =!= cur)
{
  match es {
    Nil -> {
      seg_nil_elim pl prev cur sent 1.0R;
      seg_nil_intro pl prev cur sent 1.0R;
    }
    Cons e rest -> {
      seg_cons_elim pl prev cur sent 1.0R e rest;
      refs_distinct start cur;
      seg_cons_intro pl prev cur sent 1.0R e rest;
    }
  }
}

ghost
fn rec seg_split (#a: Type0) (pl: ipayload a) (prev start sent: lref)
                 (front back: entries a)
  requires is_list_seg_ix pl prev start sent 1.0R (front @ back)
  ensures exists* (cut: lref).
    is_list_seg_s_ix pl prev start cut sent 1.0R front **
    is_list_seg_ix pl (last_or prev front) cut sent 1.0R back
  decreases front
{
  match front {
    Nil -> {
      fold (is_list_seg_s_ix pl prev start start sent 1.0R []);
    }
    Cons e rest -> {
      rewrite (is_list_seg_ix pl prev start sent 1.0R (front @ back))
        as (is_list_seg_ix pl prev start sent 1.0R (e :: (rest @ back)));
      seg_cons_elim pl prev start sent 1.0R e (rest @ back);
      with v. assert (R.pts_to start v);
      seg_split pl start (lnext v) sent rest back;
      with cut. assert (is_list_seg_s_ix pl start (lnext v) cut sent 1.0R rest);
      seg_head_distinct pl start sent (last_or start rest) cut back;
      fold (is_list_seg_s_ix pl prev start cut sent 1.0R (e :: rest));
      rewrite (is_list_seg_ix pl (last_or start rest) cut sent 1.0R back)
        as (is_list_seg_ix pl (last_or prev front) cut sent 1.0R back);
    }
  }
}

ghost
fn rec seg_merge (#a: Type0) (pl: ipayload a) (prev start cut sent: lref)
                 (front back: entries a) (#p: perm)
  requires is_list_seg_s_ix pl prev start cut sent p front **
    is_list_seg_ix pl (last_or prev front) cut sent p back
  ensures is_list_seg_ix pl prev start sent p (front @ back)
  decreases front
{
  match front {
    Nil -> {
      unfold (is_list_seg_s_ix pl prev start cut sent p []);
      rewrite (is_list_seg_ix pl (last_or prev front) cut sent p back)
        as (is_list_seg_ix pl prev start sent p (front @ back));
    }
    Cons e rest -> {
      unfold (is_list_seg_s_ix pl prev start cut sent p (e :: rest));
      with v. assert (R.pts_to start #p v);
      rewrite (is_list_seg_ix pl (last_or prev front) cut sent p back)
        as (is_list_seg_ix pl (last_or start rest) cut sent p back);
      seg_merge pl start (lnext v) cut sent rest back;
      seg_cons_intro pl prev start sent p e (rest @ back);
      rewrite (is_list_seg_ix pl prev start sent p (e :: (rest @ back)))
        as (is_list_seg_ix pl prev start sent p (front @ back));
    }
  }
}

let is_list_split_ix (#a: Type0) (pl: ipayload a) (head: lref) (p: perm)
                     (prev pos: lref) (front back: entries a) : slprop =
  exists* (hv: N.struct_list_node).
    R.pts_to head #p hv **
    is_list_seg_s_ix pl head (lnext hv) pos head p front **
    is_list_seg_ix pl prev pos head p back **
    pure (prev == last_or head front /\ lprev hv == last_or head (front @ back))

unfold let split (#a: Type0) (pl: ipayload a) (head pos: lref)
                 (front back: entries a) : slprop =
  is_list_split_ix pl head 1.0R (last_or head front) pos front back

ghost
fn split_open (#a: Type0) (pl: ipayload a) (head: lref) (front back: entries a)
  requires is_list_ring_ix pl head 1.0R (front @ back)
  ensures exists* (pos: lref). split pl head pos front back **
    pure (pos == first_or head back) ** pure ((pos == head) <==> (back == []))
{
  ring_open pl head;
  with hv. assert (R.pts_to head hv);
  seg_split pl head (lnext hv) head front back;
  with pos. assert (is_list_seg_s_ix pl head (lnext hv) pos head 1.0R front);
  seg_first pl (last_or head front) pos head;
  fold (is_list_split_ix pl head 1.0R (last_or head front) pos front back);
}

ghost
fn split_close (#a: Type0) (pl: ipayload a) (head pos: lref) (front back: entries a)
  requires split pl head pos front back
  ensures is_list_ring_ix pl head 1.0R (front @ back)
{
  unfold (is_list_split_ix pl head 1.0R (last_or head front) pos front back);
  with hv. assert (R.pts_to head hv);
  seg_merge pl head (lnext hv) pos head front back;
  ring_close pl head;
}

ghost
fn split_facts (#a: Type0) (pl: ipayload a) (head pos: lref) (front back: entries a)
  requires split pl head pos front back
  ensures split pl head pos front back **
    pure (pos == first_or head back) ** pure ((pos == head) <==> (back == []))
{
  unfold (is_list_split_ix pl head 1.0R (last_or head front) pos front back);
  seg_first pl (last_or head front) pos head;
  fold (is_list_split_ix pl head 1.0R (last_or head front) pos front back);
}

let head_rest (#a: Type0) (pl: ipayload a) (head: lref) (es: entries a)
              (hv: N.struct_list_node) : slprop =
  is_list_seg_ix pl head (lnext hv) head 1.0R es **
  pure (lprev hv == last_or head es)

ghost
fn head_open (#a: Type0) (pl: ipayload a) (head: lref) (es: entries a)
  requires is_list_ring_ix pl head 1.0R es
  ensures exists* (hv: N.struct_list_node).
    R.pts_to head hv ** head_rest pl head es hv **
    pure (lnext hv == first_or head es /\ lprev hv == last_or head es) **
    pure ((lnext hv == head) <==> (es == []))
{
  ring_open pl head;
  with hv. assert (R.pts_to head hv);
  fold (head_rest pl head es hv);
}

ghost
fn head_close (#a: Type0) (pl: ipayload a) (head: lref) (es: entries a)
              (#hv: N.struct_list_node)
  requires R.pts_to head hv ** head_rest pl head es hv
  ensures is_list_ring_ix pl head 1.0R es
{
  unfold (head_rest pl head es hv);
  ring_close pl head;
}

ghost
fn cursor_start (#a: Type0) (pl: ipayload a) (head pos: lref) (es: entries a)
                (#hv: N.struct_list_node)
  requires R.pts_to head hv ** head_rest pl head es hv ** pure (pos == lnext hv)
  ensures split pl head pos [] es
{
  unfold (head_rest pl head es hv);
  fold (is_list_seg_s_ix pl head (lnext hv) pos head 1.0R []);
  rewrite (is_list_seg_ix pl head (lnext hv) head 1.0R es)
    as (is_list_seg_ix pl head pos head 1.0R es);
  fold (is_list_split_ix pl head 1.0R (last_or #a head []) pos [] es);
}

let cursor_rest (#a: Type0) (pl: ipayload a) (head pos: lref)
                (front: entries a) (description: a) (back: entries a)
                (v: N.struct_list_node) : slprop =
  exists* (hv: N.struct_list_node).
    R.pts_to head hv **
    is_list_seg_s_ix pl head (lnext hv) pos head 1.0R front **
    is_list_seg_ix pl pos (lnext v) head 1.0R back **
    pure (pos =!= head /\ lprev v == last_or head front /\
      lprev hv == last_or head (front @ ((pos, description) :: back)))

ghost
fn cursor_expose (#a: Type0) (pl: ipayload a) (head pos: lref)
                 (front: entries a) (e: entry a) (back: entries a)
  requires split pl head pos front (e :: back)
  ensures exists* (v: N.struct_list_node).
    R.pts_to pos v ** pl pos (snd e) **
    cursor_rest pl head pos front (snd e) back v **
    pure (pos == fst e /\ pos =!= head /\ lnext v == first_or head back) **
    pure ((lnext v == head) <==> (back == []))
{
  unfold (is_list_split_ix pl head 1.0R (last_or head front) pos front (e :: back));
  seg_cons_elim pl (last_or head front) pos head 1.0R e back;
  with v. assert (R.pts_to pos v);
  seg_first pl pos (lnext v) head;
  fold (cursor_rest pl head pos front (snd e) back v);
}

ghost
fn cursor_restore (#a: Type0) (pl: ipayload a) (head pos: lref)
                  (front: entries a) (description: a) (back: entries a)
                  (#v: N.struct_list_node)
  requires R.pts_to pos v ** pl pos description **
    cursor_rest pl head pos front description back v
  ensures split pl head pos front ((pos, description) :: back)
{
  unfold (cursor_rest pl head pos front description back v);
  seg_cons_intro pl (last_or head front) pos head 1.0R (pos, description) back;
  fold (is_list_split_ix pl head 1.0R (last_or head front) pos front
    ((pos, description) :: back));
}

ghost
fn cursor_advance (#a: Type0) (pl: ipayload a) (head pos: lref)
                  (front: entries a) (description: a) (back: entries a)
                  (#v: N.struct_list_node)
  requires R.pts_to pos v ** pl pos description **
    cursor_rest pl head pos front description back v
  ensures split pl head (lnext v) (front @ [(pos, description)]) back
{
  unfold (cursor_rest pl head pos front description back v);
  seg_first pl pos (lnext v) head;
  fold (cursor_rest pl head pos front description back v);
  cursor_restore pl head pos front description back;
  split_close pl head pos front ((pos, description) :: back);
  FStar.List.Tot.Properties.append_assoc front [(pos, description)] back;
  rewrite (is_list_ring_ix pl head 1.0R (front @ ((pos, description) :: back)))
    as (is_list_ring_ix pl head 1.0R ((front @ [(pos, description)]) @ back));
  split_open pl head (front @ [(pos, description)]) back;
  with next. assert (split pl head next (front @ [(pos, description)]) back);
  rewrite (split pl head next (front @ [(pos, description)]) back)
    as (split pl head (lnext v) (front @ [(pos, description)]) back);
}

ghost
fn ops_open (#a: Type0) (pl: ipayload a) (head: lref) (es: entries a)
  requires is_list_ring_ix pl head 1.0R es
  ensures is_list_ring_ix no_payload head 1.0R es ** ipayload_of pl es
{
  ring_pl_out pl head 1.0R es;
}

ghost
fn ops_close (#a: Type0) (pl: ipayload a) (head: lref) (es: entries a)
  requires is_list_ring_ix no_payload head 1.0R es ** ipayload_of pl es
  ensures is_list_ring_ix pl head 1.0R es
{
  ring_pl_in pl head 1.0R es;
}

ghost
fn ipayload_of_cons_in (#a: Type0) (pl: ipayload a)
                      (node: lref) (description: a) (rest: entries a)
  requires pl node description ** ipayload_of pl rest
  ensures ipayload_of pl ((node, description) :: rest)
{
  fold (ipayload_of pl ((node, description) :: rest));
}

ghost
fn ipayload_of_cons_out (#a: Type0) (pl: ipayload a)
                       (node: lref) (description: a) (rest: entries a)
  requires ipayload_of pl ((node, description) :: rest)
  ensures pl node description ** ipayload_of pl rest
{
  unfold (ipayload_of pl ((node, description) :: rest));
}

ghost
fn ipayload_of_single_in (#a: Type0) (pl: ipayload a) (node: lref) (description: a)
  requires pl node description
  ensures ipayload_of pl [(node, description)]
{
  fold (ipayload_of pl []);
  ipayload_of_cons_in pl node description [];
}

ghost
fn ipayload_of_single_out (#a: Type0) (pl: ipayload a) (node: lref) (description: a)
  requires ipayload_of pl [(node, description)]
  ensures pl node description
{
  ipayload_of_cons_out pl node description [];
  unfold (ipayload_of pl []);
}

ghost
fn seg_s_cur_ne (#a: Type0) (pl: ipayload a) (prev cur endl sent: lref)
                (#p: perm) (#es: entries a)
  requires is_list_seg_s_ix pl prev cur endl sent p es
  ensures is_list_seg_s_ix pl prev cur endl sent p es **
    pure ((cur == endl) <==> (es == []))
{
  if (Nil? es) {
    rewrite (is_list_seg_s_ix pl prev cur endl sent p es)
      as (is_list_seg_s_ix pl prev cur endl sent p []);
    unfold (is_list_seg_s_ix pl prev cur endl sent p []);
    fold (is_list_seg_s_ix pl prev cur endl sent p []);
    rewrite (is_list_seg_s_ix pl prev cur endl sent p [])
      as (is_list_seg_s_ix pl prev cur endl sent p es);
  } else {
    let e = Cons?.hd es;
    let rest = Cons?.tl es;
    rewrite (is_list_seg_s_ix pl prev cur endl sent p es)
      as (is_list_seg_s_ix pl prev cur endl sent p (e :: rest));
    unfold (is_list_seg_s_ix pl prev cur endl sent p (e :: rest));
    fold (is_list_seg_s_ix pl prev cur endl sent p (e :: rest));
    rewrite (is_list_seg_s_ix pl prev cur endl sent p (e :: rest))
      as (is_list_seg_s_ix pl prev cur endl sent p es);
  }
}

ghost
fn ring_front_empty (#a: Type0) (pl: ipayload a) (head: lref)
                    (front back: entries a)
  requires is_list_ring_ix pl head 1.0R (front @ back) **
    pure (first_or head (front @ back) == first_or head back)
  ensures is_list_ring_ix pl head 1.0R (front @ back) ** pure (front == [])
{
  ring_open pl head;
  with hv. assert (R.pts_to head hv);
  seg_split pl head (lnext hv) head front back;
  with cut. assert (is_list_seg_s_ix pl head (lnext hv) cut head 1.0R front);
  seg_first pl (last_or head front) cut head;
  seg_s_cur_ne pl head (lnext hv) cut head;
  seg_merge pl head (lnext hv) cut head front back;
  ring_close pl head;
}
