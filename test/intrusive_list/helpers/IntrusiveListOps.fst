module IntrusiveListOps
open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module R = Pulse.Lib.Reference
module N = Struct_list_node
module B = IntrusiveListBase
module X = IntrusiveListIndexed
module T = Pulse.Lib.Trade

let initial (#a: Type0) (es: X.entries a) =
  match es with | [] -> [] | _::_ -> FStar.List.Tot.init es

let final (#a: Type0) (es: X.entries a { Cons? es }) = FStar.List.Tot.last es

let last_step (#a: Type0) (head: B.lref) (e: X.entry a) (es: X.entries a)
  : Lemma (X.last_or head (e::es) == X.last_or (fst e) es) =
  X.last_or_cons head e es

let last_append (#a: Type0) (head: B.lref) (xs ys: X.entries a)
  : Lemma (X.last_or head (xs @ ys) == X.last_or (X.last_or head xs) ys) =
  X.last_or_append head xs ys

let rec last_independent (#a: Type0) (head other: B.lref) (es: X.entries a)
  : Lemma (requires Cons? es) (ensures X.last_or head es == X.last_or other es)
    (decreases es) =
  match es with | [_] -> () | _::tl -> last_independent head other tl

let rec initial_final (#a: Type0) (es: X.entries a { Cons? es })
  : Lemma (es == initial es @ [final es]) (decreases es) =
  match es with | [_] -> () | _::tl -> initial_final tl

let rec last_final (#a: Type0) (head: B.lref) (es: X.entries a { Cons? es })
  : Lemma (X.last_or head es == fst (final es)) (decreases es) =
  match es with | [_] -> () | _::tl -> last_final head tl

ghost
fn refs_distinct (r1 r2: B.lref) (#v1 #v2: N.struct_list_node)
  requires R.pts_to r1 v1 ** R.pts_to r2 v2
  ensures R.pts_to r1 v1 ** R.pts_to r2 v2 ** pure (r1 =!= r2)
{
  X.refs_distinct r1 r2;
}

(* During surgery the endpoint changes; descriptions and their payloads stay
   attached to the same cells throughout this typed open-chain view. *)
let rec chain (#a: Type0) (p: X.ipayload a) (prev cur endl: B.lref) (es: X.entries a)
  : Tot slprop (decreases es) =
  match es with
  | [] -> pure (cur == endl)
  | e::tl ->
    exists* (v: N.struct_list_node).
      R.pts_to cur v ** p cur (snd e) ** pure (cur == fst e /\ B.lprev v == prev) **
      chain p cur (B.lnext v) endl tl

ghost
fn rec chain_out (#a: Type0) (p: X.ipayload a) (prev cur endl: B.lref) (es: X.entries a)
  requires X.is_list_seg_ix p prev cur endl 1.0R es
  ensures chain p prev cur endl es
  decreases es
{
  match es {
    Nil -> {
      unfold (X.is_list_seg_ix p prev cur endl 1.0R []);
      fold (chain p prev cur endl []);
    }
    Cons e tl -> {
      unfold (X.is_list_seg_ix p prev cur endl 1.0R (e::tl));
      with v. assert (R.pts_to cur v);
      chain_out p cur (B.lnext v) endl tl;
      fold (chain p prev cur endl (e::tl));
    }
  }
}

ghost
fn rec chain_in (#a: Type0) (p: X.ipayload a) (prev cur endl: B.lref) (es: X.entries a)
  (#ev: N.struct_list_node)
  requires chain p prev cur endl es ** R.pts_to endl ev
  ensures X.is_list_seg_ix p prev cur endl 1.0R es ** R.pts_to endl ev
  decreases es
{
  match es {
    Nil -> {
      unfold (chain p prev cur endl []);
      fold (X.is_list_seg_ix p prev cur endl 1.0R []);
    }
    Cons e tl -> {
      unfold (chain p prev cur endl (e::tl));
      with v. assert (R.pts_to cur v);
      refs_distinct cur endl;
      chain_in p cur (B.lnext v) endl tl;
      fold (X.is_list_seg_ix p prev cur endl 1.0R (e::tl));
    }
  }
}

ghost
fn rec chain_split (#a: Type0) (p: X.ipayload a) (prev cur endl: B.lref)
  (front back: X.entries a)
  requires chain p prev cur endl (front @ back)
  ensures exists* (mid: B.lref).
    chain p prev cur mid front ** chain p (X.last_or prev front) mid endl back
  decreases front
{
  match front {
    Nil -> { fold (chain p prev cur cur []); }
    Cons e tl -> {
      rewrite (chain p prev cur endl (front @ back))
        as (chain p prev cur endl (e::(tl @ back)));
      unfold (chain p prev cur endl (e::(tl @ back)));
      with v. assert (R.pts_to cur v);
      chain_split p cur (B.lnext v) endl tl back;
      with mid. assert (chain p cur (B.lnext v) mid tl);
      last_step prev e tl;
      rewrite (chain p (X.last_or cur tl) mid endl back)
        as (chain p (X.last_or prev front) mid endl back);
      fold (chain p prev cur mid (e::tl));
    }
  }
}

ghost
fn rec chain_join (#a: Type0) (p: X.ipayload a) (prev cur mid endl: B.lref)
  (front back: X.entries a)
  requires chain p prev cur mid front ** chain p (X.last_or prev front) mid endl back
  ensures chain p prev cur endl (front @ back)
  decreases front
{
  match front {
    Nil -> {
      unfold (chain p prev cur mid []);
      rewrite (chain p (X.last_or prev front) mid endl back)
        as (chain p prev cur endl (front @ back));
    }
    Cons e tl -> {
      unfold (chain p prev cur mid (e::tl));
      with v. assert (R.pts_to cur v);
      last_step prev e tl;
      rewrite (chain p (X.last_or prev front) mid endl back)
        as (chain p (X.last_or cur tl) mid endl back);
      chain_join p cur (B.lnext v) mid endl tl back;
      fold (chain p prev cur endl (e::(tl @ back)));
    }
  }
}

ghost
fn chain_first (#a: Type0) (p: X.ipayload a) (prev cur endl: B.lref) (es: X.entries a)
  requires chain p prev cur endl es
  ensures chain p prev cur endl es ** pure (cur == X.first_or endl es)
{
  match es {
    Nil -> { unfold (chain p prev cur endl []); fold (chain p prev cur endl []); }
    Cons e tl -> {
      unfold (chain p prev cur endl (e::tl));
      fold (chain p prev cur endl (e::tl));
    }
  }
}

ghost
fn chain_peel (#a: Type0) (p: X.ipayload a) (prev cur endl: B.lref)
  (es: X.entries a { Cons? es })
  requires chain p prev cur endl es
  ensures exists* (v: N.struct_list_node).
    chain p prev cur (fst (final es)) (initial es) **
    R.pts_to (fst (final es)) v ** p (fst (final es)) (snd (final es)) **
    pure (B.lnext v == endl /\ B.lprev v == X.last_or prev (initial es))
{
  initial_final es;
  rewrite (chain p prev cur endl es)
    as (chain p prev cur endl (initial es @ [final es]));
  chain_split p prev cur endl (initial es) [final es];
  with mid. assert (chain p (X.last_or prev (initial es)) mid endl [final es]);
  unfold (chain p (X.last_or prev (initial es)) mid endl [final es]);
  with v. assert (R.pts_to mid v);
  unfold (chain p mid (B.lnext v) endl []);
  rewrite (R.pts_to mid v) as (R.pts_to (fst (final es)) v);
  rewrite (p mid (snd (final es))) as (p (fst (final es)) (snd (final es)));
  rewrite (chain p prev cur mid (initial es))
    as (chain p prev cur (fst (final es)) (initial es));
}

ghost
fn chain_snoc (#a: Type0) (p: X.ipayload a) (prev cur endl last: B.lref)
  (es: X.entries a) (d: a) (#v: N.struct_list_node)
  requires chain p prev cur last es ** R.pts_to last v ** p last d **
    pure (B.lnext v == endl /\ B.lprev v == X.last_or prev es)
  ensures chain p prev cur endl (es @ [(last,d)])
{
  fold (chain p last (B.lnext v) endl []);
  fold (chain p (X.last_or prev es) last endl [(last,d)]);
  chain_join p prev cur last endl es [(last,d)];
}

ghost
fn ring_open (#a: Type0) (p: X.ipayload a) (head: B.lref) (es: X.entries a)
  requires X.is_list_ring_ix p head 1.0R es
  ensures exists* (v: N.struct_list_node).
    R.pts_to head v ** chain p head (B.lnext v) head es **
    pure (B.lprev v == X.last_or head es) **
    pure (B.lnext v == X.first_or head es) **
    pure ((B.lnext v == head) <==> (es == [])) **
    pure ((B.lprev v == head) <==> (es == []))
{
  X.ring_open p head;
  with v. assert (R.pts_to head v);
  chain_out p head (B.lnext v) head es;
}

ghost
fn ring_close (#a: Type0) (p: X.ipayload a) (head: B.lref) (es: X.entries a)
  (#v: N.struct_list_node)
  requires R.pts_to head v ** chain p head (B.lnext v) head es **
    pure (B.lprev v == X.last_or head es)
  ensures X.is_list_ring_ix p head 1.0R es
{
  chain_in p head (B.lnext v) head es;
  fold (X.is_list_ring_ix p head 1.0R es);
}

let prefix (#a: Type0) (p: X.ipayload a) (head prev endl: B.lref)
  (es: X.entries a) (hp: B.lref) : slprop =
  exists* (hv: N.struct_list_node).
    R.pts_to head hv ** chain p head (B.lnext hv) endl es **
    pure (prev == X.last_or head es /\ B.lprev hv == hp)

let tail_rest (#a: Type0) (p: X.ipayload a) (head prev: B.lref)
  (es: X.entries a) (hp pp: B.lref) : slprop =
  match es with
  | [] -> pure (prev == head /\ pp == hp)
  | _::_ ->
    exists* (hv: N.struct_list_node).
      R.pts_to head hv ** chain p head (B.lnext hv) prev (initial es) **
      p prev (snd (final es)) **
      pure (prev == fst (final es) /\ B.lprev hv == hp /\
        pp == X.last_or head (initial es))

ghost
fn tail_open (#a: Type0) (p: X.ipayload a) (head prev endl: B.lref)
  (es: X.entries a) (hp: B.lref)
  requires prefix p head prev endl es hp
  ensures exists* (v: N.struct_list_node).
    R.pts_to prev v ** tail_rest p head prev es hp (B.lprev v) **
    pure (B.lnext v == endl /\ prev == X.last_or head es)
{
  unfold (prefix p head prev endl es hp);
  with hv. assert (R.pts_to head hv);
  match es {
    Nil -> {
      unfold (chain p head (B.lnext hv) endl []);
      rewrite (R.pts_to head hv) as (R.pts_to prev hv);
      fold (tail_rest p head prev [] hp (B.lprev hv));
    }
    Cons e tl -> {
      last_final head es;
      chain_peel p head (B.lnext hv) endl es;
      with v. assert (R.pts_to (fst (final es)) v);
      rewrite (R.pts_to (fst (final es)) v) as (R.pts_to prev v);
      rewrite (p (fst (final es)) (snd (final es))) as (p prev (snd (final es)));
      rewrite (chain p head (B.lnext hv) (fst (final es)) (initial es))
        as (chain p head (B.lnext hv) prev (initial es));
      fold (tail_rest p head prev es hp (B.lprev v));
    }
  }
}

ghost
fn tail_close (#a: Type0) (p: X.ipayload a) (head prev endl: B.lref)
  (es: X.entries a) (hp: B.lref) (#pp: B.lref) (#v: N.struct_list_node)
  requires R.pts_to prev v ** tail_rest p head prev es hp pp **
    pure (B.lnext v == endl /\ B.lprev v == pp)
  ensures prefix p head prev endl es hp
{
  match es {
    Nil -> {
      unfold (tail_rest p head prev [] hp pp);
      rewrite (R.pts_to prev v) as (R.pts_to head v);
      fold (chain p head (B.lnext v) endl []);
      fold (prefix p head prev endl es hp);
    }
    Cons e tl -> {
      unfold (tail_rest p head prev es hp pp);
      with hv. assert (R.pts_to head hv);
      chain_snoc p head (B.lnext hv) endl prev (initial es) (snd (final es));
      initial_final es;
      last_final head es;
      rewrite (chain p head (B.lnext hv) endl (initial es @ [(prev,snd (final es))]))
        as (chain p head (B.lnext hv) endl es);
      fold (prefix p head prev endl es hp);
    }
  }
}

let insert_cut (#a: Type0) (p: X.ipayload a) (head prev next: B.lref)
  (front back: X.entries a) : slprop =
  prefix p head prev next front (X.last_or head (front @ back)) **
  chain p prev next head back

ghost
fn position_open (#a: Type0) (p: X.ipayload a) (head pos: B.lref)
  (front back: X.entries a)
  requires X.is_list_ring_ix p head 1.0R (front @ back) **
    pure (pos == X.last_or head front)
  ensures exists* (v: N.struct_list_node).
    R.pts_to pos v ** T.trade (R.pts_to pos v)
      (insert_cut p head pos (B.lnext v) front back)
{
  ring_open p head (front @ back);
  with hv. assert (R.pts_to head hv);
  chain_split p head (B.lnext hv) head front back;
  with next. assert (chain p head (B.lnext hv) next front);
  rewrite (chain p (X.last_or head front) next head back)
    as (chain p pos next head back);
  fold (prefix p head pos next front (X.last_or head (front @ back)));
  tail_open p head pos next front (X.last_or head (front @ back));
  with v. assert (R.pts_to pos v);
  intro (T.trade (R.pts_to pos v) (insert_cut p head pos (B.lnext v) front back))
    #(tail_rest p head pos front (X.last_or head (front @ back)) (B.lprev v) **
      chain p pos next head back)
  fn _ {
    tail_close p head pos (B.lnext v) front (X.last_or head (front @ back));
    rewrite (chain p pos next head back) as (chain p pos (B.lnext v) head back);
    fold (insert_cut p head pos (B.lnext v) front back);
  };
}

ghost
fn position_close (#a: Type0) (p: X.ipayload a) (head pos next: B.lref)
  (front back: X.entries a) (#v: N.struct_list_node)
  requires R.pts_to pos v ** T.trade (R.pts_to pos v)
    (insert_cut p head pos (B.lnext v) front back) ** pure (next == B.lnext v)
  ensures insert_cut p head pos next front back
{
  T.elim_trade (R.pts_to pos v) (insert_cut p head pos (B.lnext v) front back);
  rewrite (insert_cut p head pos (B.lnext v) front back)
    as (insert_cut p head pos next front back);
}

let last_suffix (#a: Type0) (head: B.lref) (front back: X.entries a)
  : Lemma (requires Cons? back)
    (ensures X.last_or head (front @ back) == X.last_or head back) =
  last_append head front back;
  last_independent head (X.last_or head front) back

let add_next_rest (#a: Type0) (p: X.ipayload a) (head prev next: B.lref)
  (front back: X.entries a) (nx: B.lref) : slprop =
  match back with
  | [] -> chain p head nx head front **
    pure (next == head /\ prev == X.last_or head front)
  | e::tl ->
    prefix p head prev next front (X.last_or head (front @ back)) **
    p next (snd e) ** chain p next nx head tl ** pure (next == fst e)

ghost
fn add_expose_next (#a: Type0) (p: X.ipayload a) (head prev next: B.lref)
  (front back: X.entries a)
  requires insert_cut p head prev next front back
  ensures exists* (v: N.struct_list_node).
    R.pts_to next v ** add_next_rest p head prev next front back (B.lnext v)
{
  unfold (insert_cut p head prev next front back);
  match back {
    Nil -> {
      unfold (chain p prev next head []);
      unfold (prefix p head prev next front (X.last_or head (front @ back)));
      with hv. assert (R.pts_to head hv);
      rewrite (R.pts_to head hv) as (R.pts_to next hv);
      rewrite (chain p head (B.lnext hv) next front)
        as (chain p head (B.lnext hv) head front);
      fold (add_next_rest p head prev next front back (B.lnext hv));
    }
    Cons e tl -> {
      unfold (chain p prev next head (e::tl));
      with v. assert (R.pts_to next v);
      fold (add_next_rest p head prev next front back (B.lnext v));
    }
  }
}

let add_prev_rest (#a: Type0) (p: X.ipayload a) (head prev next entry: B.lref)
  (d: a) (front back: X.entries a) (pp: B.lref) : slprop =
  tail_rest p head prev front (X.last_or head (front @ ((entry,d)::back))) pp **
  chain p entry next head back

ghost
fn add_reseat (#a: Type0) (p: X.ipayload a) (head prev next entry: B.lref)
  (d: a) (front back: X.entries a) (#nx: B.lref) (#nv: N.struct_list_node)
  requires R.pts_to next nv ** add_next_rest p head prev next front back nx **
    pure (B.lnext nv == nx /\ B.lprev nv == entry)
  ensures exists* (pv: N.struct_list_node).
    R.pts_to prev pv ** add_prev_rest p head prev next entry d front back (B.lprev pv)
{
  match back {
    Nil -> {
      unfold (add_next_rest p head prev next front back nx);
      rewrite (R.pts_to next nv) as (R.pts_to head nv);
      rewrite (chain p head nx head front) as (chain p head (B.lnext nv) next front);
      last_append head front [(entry,d)];
      fold (prefix p head prev next front (X.last_or head (front @ ((entry,d)::back))));
      tail_open p head prev next front (X.last_or head (front @ ((entry,d)::back)));
      with pv. assert (R.pts_to prev pv);
      fold (chain p entry next head []);
      fold (add_prev_rest p head prev next entry d front back (B.lprev pv));
    }
    Cons e tl -> {
      unfold (add_next_rest p head prev next front back nx);
      rewrite (chain p next nx head tl) as (chain p next (B.lnext nv) head tl);
      fold (chain p entry next head (e::tl));
      last_suffix head front back;
      last_suffix head front ((entry,d)::back);
      last_step head (entry,d) back;
      last_independent head entry back;
      rewrite (prefix p head prev next front (X.last_or head (front @ back)))
        as (prefix p head prev next front (X.last_or head (front @ ((entry,d)::back))));
      tail_open p head prev next front (X.last_or head (front @ ((entry,d)::back)));
      with pv. assert (R.pts_to prev pv);
      fold (add_prev_rest p head prev next entry d front back (B.lprev pv));
    }
  }
}

ghost
fn add_close (#a: Type0) (p: X.ipayload a) (head prev next entry: B.lref)
  (d: a) (front back: X.entries a) (#pp: B.lref) (#pv #ev: N.struct_list_node)
  requires R.pts_to prev pv ** add_prev_rest p head prev next entry d front back pp **
    R.pts_to entry ev ** p entry d **
    pure (B.lnext pv == entry /\ B.lprev pv == pp /\
      B.lnext ev == next /\ B.lprev ev == prev)
  ensures X.is_list_ring_ix p head 1.0R (front @ ((entry,d)::back))
{
  unfold (add_prev_rest p head prev next entry d front back pp);
  tail_close p head prev entry front (X.last_or head (front @ ((entry,d)::back)));
  unfold (prefix p head prev entry front (X.last_or head (front @ ((entry,d)::back))));
  with hv. assert (R.pts_to head hv);
  rewrite (chain p entry next head back) as (chain p entry (B.lnext ev) head back);
  fold (chain p prev entry head ((entry,d)::back));
  rewrite (chain p prev entry head ((entry,d)::back))
    as (chain p (X.last_or head front) entry head ((entry,d)::back));
  chain_join p head (B.lnext hv) entry head front ((entry,d)::back);
  ring_close p head (front @ ((entry,d)::back));
}

let del_cut (#a: Type0) (p: X.ipayload a) (head prev next entry: B.lref)
  (d: a) (front back: X.entries a) : slprop =
  prefix p head prev entry front (X.last_or head (front @ ((entry,d)::back))) **
  chain p entry next head back

ghost
fn del_open (#a: Type0) (p: X.ipayload a) (head entry: B.lref)
  (d: a) (front back: X.entries a)
  requires X.is_list_ring_ix p head 1.0R (front @ ((entry,d)::back))
  ensures exists* (ev: N.struct_list_node).
    R.pts_to entry ev ** p entry d ** del_cut p head (B.lprev ev) (B.lnext ev) entry d front back
{
  ring_open p head (front @ ((entry,d)::back));
  with hv. assert (R.pts_to head hv);
  chain_split p head (B.lnext hv) head front ((entry,d)::back);
  with cur. assert (chain p (X.last_or head front) cur head ((entry,d)::back));
  unfold (chain p (X.last_or head front) cur head ((entry,d)::back));
  with ev. assert (R.pts_to cur ev);
  rewrite (R.pts_to cur ev) as (R.pts_to entry ev);
  rewrite (p cur d) as (p entry d);
  rewrite (chain p cur (B.lnext ev) head back) as (chain p entry (B.lnext ev) head back);
  rewrite (chain p head (B.lnext hv) cur front) as (chain p head (B.lnext hv) entry front);
  fold (prefix p head (B.lprev ev) entry front (X.last_or head (front @ ((entry,d)::back))));
  fold (del_cut p head (B.lprev ev) (B.lnext ev) entry d front back);
}

ghost
fn del_cut_pin (#a: Type0) (p: X.ipayload a) (head prev next entry: B.lref)
  (d: a) (front back: X.entries a) (#pv #nx: B.lref)
  requires del_cut p head pv nx entry d front back ** pure (prev == pv /\ next == nx)
  ensures del_cut p head prev next entry d front back
{
  rewrite (del_cut p head pv nx entry d front back)
    as (del_cut p head prev next entry d front back);
}

ghost
fn tail_alias (#a: Type0) (p: X.ipayload a) (head prev next entry: B.lref)
  (front back: X.entries a) (hp pp: B.lref) (#pv: N.struct_list_node)
  requires R.pts_to prev pv ** tail_rest p head prev front hp pp **
    chain p entry next head back
  ensures R.pts_to prev pv ** tail_rest p head prev front hp pp **
    chain p entry next head back ** pure ((prev == next) <==> (front @ back == []))
{
  match back {
    Nil -> {
      unfold (chain p entry next head []);
      fold (chain p entry next head []);
      match front {
        Nil -> {
          unfold (tail_rest p head prev [] hp pp);
          fold (tail_rest p head prev [] hp pp);
        }
        Cons e tl -> {
          unfold (tail_rest p head prev front hp pp);
          with hv. assert (R.pts_to head hv);
          refs_distinct prev head;
          fold (tail_rest p head prev front hp pp);
        }
      }
    }
    Cons e tl -> {
      unfold (chain p entry next head (e::tl));
      with nv. assert (R.pts_to next nv);
      refs_distinct prev next;
      fold (chain p entry next head (e::tl));
    }
  }
}

let del_prev_rest (#a: Type0) (p: X.ipayload a) (head prev next entry: B.lref)
  (d: a) (front back: X.entries a) (pp: B.lref) : slprop =
  tail_rest p head prev front (X.last_or head (front @ ((entry,d)::back))) pp **
  chain p entry next head back

ghost
fn del_expose_prev (#a: Type0) (p: X.ipayload a) (head prev next entry: B.lref)
  (d: a) (front back: X.entries a)
  requires del_cut p head prev next entry d front back
  ensures exists* (pv: N.struct_list_node).
    R.pts_to prev pv ** del_prev_rest p head prev next entry d front back (B.lprev pv) **
    pure (B.lnext pv == entry /\ prev == X.last_or head front /\
      next == X.first_or head back /\ ((prev == next) <==> (front @ back == [])))
{
  unfold (del_cut p head prev next entry d front back);
  chain_first p entry next head back;
  tail_open p head prev entry front (X.last_or head (front @ ((entry,d)::back)));
  with pv. assert (R.pts_to prev pv);
  tail_alias p head prev next entry front back
    (X.last_or head (front @ ((entry,d)::back))) (B.lprev pv);
  fold (del_prev_rest p head prev next entry d front back (B.lprev pv));
}

let del_next_rest (#a: Type0) (p: X.ipayload a) (head prev next entry: B.lref)
  (d: a) (front back: X.entries a) (nx: B.lref) : slprop =
  match back with
  | [] -> chain p head nx head front **
    pure (next == head /\ prev == X.last_or head front)
  | e::tl ->
    prefix p head prev next front (X.last_or head (front @ ((entry,d)::back))) **
    p next (snd e) ** chain p next nx head tl ** pure (next == fst e)

ghost
fn del_reseat_next (#a: Type0) (p: X.ipayload a) (head prev next entry: B.lref)
  (d: a) (front back: X.entries a) (#pp: B.lref) (#pv: N.struct_list_node)
  requires R.pts_to prev pv ** del_prev_rest p head prev next entry d front back pp **
    pure (B.lnext pv == next /\ B.lprev pv == pp)
  ensures exists* (nv: N.struct_list_node).
    R.pts_to next nv ** del_next_rest p head prev next entry d front back (B.lnext nv)
{
  unfold (del_prev_rest p head prev next entry d front back pp);
  tail_close p head prev next front (X.last_or head (front @ ((entry,d)::back)));
  match back {
    Nil -> {
      unfold (chain p entry next head []);
      unfold (prefix p head prev next front (X.last_or head (front @ ((entry,d)::back))));
      with hv. assert (R.pts_to head hv);
      rewrite (R.pts_to head hv) as (R.pts_to next hv);
      rewrite (chain p head (B.lnext hv) next front) as (chain p head (B.lnext hv) head front);
      fold (del_next_rest p head prev next entry d front back (B.lnext hv));
    }
    Cons e tl -> {
      unfold (chain p entry next head (e::tl));
      with nv. assert (R.pts_to next nv);
      fold (del_next_rest p head prev next entry d front back (B.lnext nv));
    }
  }
}

ghost
fn del_close_next (#a: Type0) (p: X.ipayload a) (head prev next entry: B.lref)
  (d: a) (front back: X.entries a) (#nx: B.lref) (#nv: N.struct_list_node)
  requires R.pts_to next nv ** del_next_rest p head prev next entry d front back nx **
    pure (B.lnext nv == nx /\ B.lprev nv == prev)
  ensures X.is_list_ring_ix p head 1.0R (front @ back)
{
  match back {
    Nil -> {
      unfold (del_next_rest p head prev next entry d front back nx);
      rewrite (R.pts_to next nv) as (R.pts_to head nv);
      FStar.List.Tot.Properties.append_l_nil front;
      rewrite (chain p head nx head front) as (chain p head (B.lnext nv) head (front @ back));
      ring_close p head (front @ back);
    }
    Cons e tl -> {
      unfold (del_next_rest p head prev next entry d front back nx);
      rewrite (chain p next nx head tl) as (chain p next (B.lnext nv) head tl);
      fold (chain p prev next head (e::tl));
      unfold (prefix p head prev next front (X.last_or head (front @ ((entry,d)::back))));
      with hv. assert (R.pts_to head hv);
      rewrite (chain p prev next head back) as (chain p (X.last_or head front) next head back);
      chain_join p head (B.lnext hv) next head front back;
      last_suffix head front back;
      last_suffix head front ((entry,d)::back);
      last_step head (entry,d) back;
      last_independent head entry back;
      ring_close p head (front @ back);
    }
  }

}

let move_rest0 (#a: Type0) (p: X.ipayload a) (source destination first last tail: B.lref)
  (src dst: X.entries a) (pp: B.lref) : slprop =
  X.is_list_ring_ix p source 1.0R src ** tail_rest p destination tail dst tail pp **
  pure (Cons? src /\ first == X.first_or source src /\ last == X.last_or source src)

ghost
fn move_open (#a: Type0) (p: X.ipayload a) (source destination first last tail: B.lref)
  (src dst: X.entries a)
  requires X.is_list_ring_ix p source 1.0R src ** X.is_list_ring_ix p destination 1.0R dst **
    pure (Cons? src /\ first == X.first_or source src /\
      last == X.last_or source src /\ tail == X.last_or destination dst)
  ensures exists* (tv: N.struct_list_node).
    R.pts_to tail tv ** move_rest0 p source destination first last tail src dst (B.lprev tv) **
    pure (B.lnext tv == destination)
{
  ring_open p destination dst;
  with dv. assert (R.pts_to destination dv);
  fold (prefix p destination tail destination dst tail);
  tail_open p destination tail destination dst tail;
  with tv. assert (R.pts_to tail tv);
  fold (move_rest0 p source destination first last tail src dst (B.lprev tv));
}

let move_rest1 (#a: Type0) (p: X.ipayload a) (source destination first last tail: B.lref)
  (src dst: X.entries a) (nx: B.lref) : slprop =
  (exists* (sv: N.struct_list_node). R.pts_to source sv) **
  prefix p destination tail first dst tail **
  (match src with
   | [] -> pure False
   | e::rest ->
     p first (snd e) ** chain p first nx source rest **
     pure (first == fst e /\ last == X.last_or source src))

ghost
fn move_first (#a: Type0) (p: X.ipayload a) (source destination first last tail: B.lref)
  (src dst: X.entries a) (#pp: B.lref) (#tv: N.struct_list_node)
  requires R.pts_to tail tv ** move_rest0 p source destination first last tail src dst pp **
    pure (B.lnext tv == first /\ B.lprev tv == pp)
  ensures exists* (fv: N.struct_list_node).
    R.pts_to first fv ** move_rest1 p source destination first last tail src dst (B.lnext fv) **
    pure (B.lprev fv == source)
{
  unfold (move_rest0 p source destination first last tail src dst pp);
  tail_close p destination tail first dst tail;
  ring_open p source src;
  with sv. assert (R.pts_to source sv);
  match src {
    Nil -> { unreachable (); }
    Cons e rest -> {
      unfold (chain p source (B.lnext sv) source (e::rest));
      with fv. assert (R.pts_to (B.lnext sv) fv);
      rewrite (R.pts_to (B.lnext sv) fv) as (R.pts_to first fv);
      rewrite (p (B.lnext sv) (snd e)) as (p first (snd e));
      rewrite (chain p (B.lnext sv) (B.lnext fv) source rest)
        as (chain p first (B.lnext fv) source rest);
      fold (move_rest1 p source destination first last tail src dst (B.lnext fv));
    }
  }
}

let move_rest2 (#a: Type0) (p: X.ipayload a) (source destination first last tail: B.lref)
  (src dst: X.entries a) (lp: B.lref) : slprop =
  (exists* (sv: N.struct_list_node). R.pts_to source sv) **
  prefix p destination tail first dst tail **
  (match src with
   | [] -> pure False
   | _::_ ->
     chain p tail first last (initial src) ** p last (snd (final src)) **
     pure (last == fst (final src) /\ lp == X.last_or tail (initial src)))

ghost
fn move_last (#a: Type0) (p: X.ipayload a) (source destination first last tail: B.lref)
  (src dst: X.entries a) (#nx: B.lref) (#fv: N.struct_list_node)
  requires R.pts_to first fv ** move_rest1 p source destination first last tail src dst nx **
    pure (B.lnext fv == nx /\ B.lprev fv == tail)
  ensures exists* (lv: N.struct_list_node).
    R.pts_to last lv ** move_rest2 p source destination first last tail src dst (B.lprev lv) **
    pure (B.lnext lv == source)
{
  unfold (move_rest1 p source destination first last tail src dst nx);
  match src {
    Nil -> { unreachable (); }
    Cons e rest -> {
      rewrite (chain p first nx source rest) as (chain p first (B.lnext fv) source rest);
      fold (chain p tail first source (e::rest));
      chain_peel p tail first source src;
      last_final source src;
      with lv. assert (R.pts_to (fst (final src)) lv);
      rewrite (R.pts_to (fst (final src)) lv) as (R.pts_to last lv);
      rewrite (p (fst (final src)) (snd (final src))) as (p last (snd (final src)));
      rewrite (chain p tail first (fst (final src)) (initial src))
        as (chain p tail first last (initial src));
      fold (move_rest2 p source destination first last tail src dst (B.lprev lv));
    }
  }
}

let move_rest3 (#a: Type0) (p: X.ipayload a) (source destination first last tail: B.lref)
  (src dst: X.entries a) (dn: B.lref) : slprop =
  (exists* (sv: N.struct_list_node). R.pts_to source sv) **
  chain p destination dn first dst ** chain p tail first destination src **
  pure (Cons? src /\ last == X.last_or destination src /\ tail == X.last_or destination dst)

ghost
fn move_destination (#a: Type0) (p: X.ipayload a)
  (source destination first last tail: B.lref) (src dst: X.entries a)
  (#lp: B.lref) (#lv: N.struct_list_node)
  requires R.pts_to last lv ** move_rest2 p source destination first last tail src dst lp **
    pure (B.lnext lv == destination /\ B.lprev lv == lp)
  ensures exists* (dv: N.struct_list_node).
    R.pts_to destination dv ** move_rest3 p source destination first last tail src dst (B.lnext dv)
{
  unfold (move_rest2 p source destination first last tail src dst lp);
  match src {
    Nil -> { unreachable (); }
    Cons e rest -> {
      chain_snoc p tail first destination last (initial src) (snd (final src));
      initial_final src;
      last_final destination src;
      rewrite (chain p tail first destination (initial src @ [(last,snd (final src))]))
        as (chain p tail first destination src);
      unfold (prefix p destination tail first dst tail);
      with dv. assert (R.pts_to destination dv);
      fold (move_rest3 p source destination first last tail src dst (B.lnext dv));
    }
  }
}

ghost
fn move_close (#a: Type0) (p: X.ipayload a) (source destination first last tail: B.lref)
  (src dst: X.entries a) (#dn: B.lref) (#dv: N.struct_list_node)
  requires R.pts_to destination dv ** move_rest3 p source destination first last tail src dst dn **
    pure (B.lnext dv == dn /\ B.lprev dv == last)
  ensures R.pts_to_uninit source ** X.is_list_ring_ix p destination 1.0R (dst @ src)
{
  unfold (move_rest3 p source destination first last tail src dst dn);
  rewrite (chain p destination dn first dst) as (chain p destination (B.lnext dv) first dst);
  rewrite (chain p tail first destination src)
    as (chain p (X.last_or destination dst) first destination src);
  chain_join p destination (B.lnext dv) first destination dst src;
  last_suffix destination dst src;
  ring_close p destination (dst @ src);
}

ghost
fn indexed_init (#a: Type0) (p: X.ipayload a) (head: B.lref)
  requires R.pts_to head (B.mklink head head)
  ensures X.is_list_ring_ix p head 1.0R []
{
  fold (chain p head head head []);
  ring_close p head [];
}

ghost
fn move_empty (#a: Type0) (p: X.ipayload a) (source destination: B.lref) (src dst: X.entries a)
  requires X.is_list_ring_ix p source 1.0R src ** X.is_list_ring_ix p destination 1.0R dst **
    pure (src == [])
  ensures X.is_list_ring_ix p source 1.0R [] **
    X.is_list_ring_ix p destination 1.0R (dst @ src)
{
  FStar.List.Tot.Properties.append_l_nil dst;
  rewrite (X.is_list_ring_ix p source 1.0R src) as (X.is_list_ring_ix p source 1.0R []);
  rewrite (X.is_list_ring_ix p destination 1.0R dst)
    as (X.is_list_ring_ix p destination 1.0R (dst @ src));
}

let nonempty_ring (#a: Type0) (p: X.ipayload a) (head: B.lref) (es: X.entries a) : slprop =
  X.is_list_ring_ix p head 1.0R es ** pure (Cons? es)

ghost
fn nonempty_intro (#a: Type0) (p: X.ipayload a) (head: B.lref) (es: X.entries a)
  requires X.is_list_ring_ix p head 1.0R es ** pure (es =!= [])
  ensures nonempty_ring p head es
{
  fold (nonempty_ring p head es);
}

ghost
fn nonempty_elim (#a: Type0) (p: X.ipayload a) (head: B.lref) (es: X.entries a)
  requires nonempty_ring p head es
  ensures X.is_list_ring_ix p head 1.0R es ** pure (Cons? es)
{
  unfold (nonempty_ring p head es);
}
