module IntrusiveListOps
open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module R = Pulse.Lib.Reference
module N = Struct_list_node
module L = IntrusiveList
module T = Pulse.Lib.Trade

unfold let initial (cs: list L.lref) =
  match cs with | [] -> [] | _::_ -> L.finit cs
unfold let final (cs: list L.lref) =
  match cs with | [] -> R.null | _::_ -> L.flast cs
unfold let rest (cs: list L.lref) =
  match cs with | [] -> [] | _::tl -> tl

(* The open chain permits changing its endpoint before closing the ring. *)
let rec chain (pl: L.payload) (prev cur endl: L.lref) (cs: list L.lref)
  : Tot slprop (decreases cs) =
  match cs with
  | [] -> pure (cur == endl)
  | c::tl ->
    exists* (v: N.struct_list_node).
      R.pts_to cur v ** pl cur ** pure (cur == c /\ L.lprev v == prev) **
      chain pl cur (L.lnext v) endl tl

ghost
fn rec chain_out (pl: L.payload) (prev cur endl: L.lref) (cs: list L.lref)
  requires L.is_list_seg_with pl prev cur endl 1.0R cs
  ensures chain pl prev cur endl cs
  decreases cs
{
  match cs {
    Nil -> {
      unfold (L.is_list_seg_with pl prev cur endl 1.0R []);
      fold (chain pl prev cur endl []);
    }
    Cons c tl -> {
      L.seg_cons_elim pl prev cur endl 1.0R c tl;
      with v. assert (R.pts_to cur v);
      chain_out pl cur (L.lnext v) endl tl;
      fold (chain pl prev cur endl (c::tl));
    }
  }
}

ghost
fn rec chain_in (pl: L.payload) (prev cur endl: L.lref) (cs: list L.lref)
  (#ev: N.struct_list_node)
  requires chain pl prev cur endl cs ** R.pts_to endl ev
  ensures L.is_list_seg_with pl prev cur endl 1.0R cs ** R.pts_to endl ev
  decreases cs
{
  match cs {
    Nil -> {
      unfold (chain pl prev cur endl []);
      L.seg_nil_intro pl prev cur endl 1.0R;
    }
    Cons c tl -> {
      unfold (chain pl prev cur endl (c::tl));
      with v. assert (R.pts_to cur v);
      L.refs_distinct cur endl;
      chain_in pl cur (L.lnext v) endl tl;
      L.seg_cons_intro pl prev cur endl 1.0R c tl;
    }
  }
}

ghost
fn rec chain_split (pl: L.payload) (prev cur endl: L.lref) (front back: list L.lref)
  requires chain pl prev cur endl (front @ back)
  ensures exists* (mid: L.lref).
    chain pl prev cur mid front ** chain pl (L.last_or prev front) mid endl back
  decreases front
{
  match front {
    Nil -> {
      fold (chain pl prev cur cur []);
    }
    Cons c tl -> {
      rewrite (chain pl prev cur endl (front @ back))
        as (chain pl prev cur endl (c::(tl @ back)));
      unfold (chain pl prev cur endl (c::(tl @ back)));
      with v. assert (R.pts_to cur v);
      chain_split pl cur (L.lnext v) endl tl back;
      with mid. assert (chain pl cur (L.lnext v) mid tl);
      L.last_or_cons prev c tl;
      rewrite (chain pl (L.last_or cur tl) mid endl back)
        as (chain pl (L.last_or prev front) mid endl back);
      fold (chain pl prev cur mid (c::tl));
    }
  }
}

ghost
fn rec chain_join (pl: L.payload) (prev cur mid endl: L.lref) (front back: list L.lref)
  requires chain pl prev cur mid front ** chain pl (L.last_or prev front) mid endl back
  ensures chain pl prev cur endl (front @ back)
  decreases front
{
  match front {
    Nil -> {
      unfold (chain pl prev cur mid []);
      rewrite (chain pl (L.last_or prev front) mid endl back)
        as (chain pl prev cur endl (front @ back));
    }
    Cons c tl -> {
      unfold (chain pl prev cur mid (c::tl));
      with v. assert (R.pts_to cur v);
      L.last_or_cons prev c tl;
      rewrite (chain pl (L.last_or prev front) mid endl back)
        as (chain pl (L.last_or cur tl) mid endl back);
      chain_join pl cur (L.lnext v) mid endl tl back;
      fold (chain pl prev cur endl (c::(tl @ back)));
    }
  }
}

ghost
fn chain_peel (pl: L.payload) (prev cur endl: L.lref) (cs: list L.lref { Cons? cs })
  requires chain pl prev cur endl cs ** pure (Cons? cs)
  ensures exists* (v: N.struct_list_node).
    chain pl prev cur (L.flast cs) (L.finit cs) **
    R.pts_to (L.flast cs) v ** pl (L.flast cs) **
    pure (L.lnext v == endl /\ L.lprev v == L.last_or prev (L.finit cs))
{
  L.finit_flast_append cs;
  rewrite (chain pl prev cur endl cs)
    as (chain pl prev cur endl (L.finit cs @ [L.flast cs]));
  chain_split pl prev cur endl (L.finit cs) [L.flast cs];
  with mid. assert (chain pl (L.last_or prev (L.finit cs)) mid endl [L.flast cs]);
  unfold (chain pl (L.last_or prev (L.finit cs)) mid endl [L.flast cs]);
  with v. assert (R.pts_to mid v);
  unfold (chain pl mid (L.lnext v) endl []);
  rewrite (R.pts_to mid v) as (R.pts_to (L.flast cs) v);
  rewrite (pl mid) as (pl (L.flast cs));
  rewrite (chain pl prev cur mid (L.finit cs))
    as (chain pl prev cur (L.flast cs) (L.finit cs));
}

ghost
fn chain_snoc (pl: L.payload) (prev cur endl last: L.lref) (cs: list L.lref)
  (#v: N.struct_list_node)
  requires chain pl prev cur last cs ** R.pts_to last v ** pl last **
    pure (L.lnext v == endl /\ L.lprev v == L.last_or prev cs)
  ensures chain pl prev cur endl (cs @ [last])
{
  fold (chain pl last (L.lnext v) endl []);
  fold (chain pl (L.last_or prev cs) last endl [last]);
  chain_join pl prev cur last endl cs [last];
}

ghost
fn ring_chain_out (pl: L.payload) (head: L.lref) (cs: list L.lref)
  requires L.is_list_ring_with pl head 1.0R cs
  ensures exists* (v: N.struct_list_node).
    R.pts_to head v ** chain pl head (L.lnext v) head cs **
    pure (L.lprev v == L.last_or head cs)
{
  L.ring_open pl head;
  with v. assert (R.pts_to head v);
  chain_out pl head (L.lnext v) head cs;
}

ghost
fn ring_chain_in (pl: L.payload) (head: L.lref) (cs: list L.lref)
  (#v: N.struct_list_node)
  requires R.pts_to head v ** chain pl head (L.lnext v) head cs **
    pure (L.lprev v == L.last_or head cs)
  ensures L.is_list_ring_with pl head 1.0R cs
{
  chain_in pl head (L.lnext v) head cs;
  L.ring_close pl head;
}

ghost
fn position_open (pl: L.payload) (head pos: L.lref) (front back: list L.lref)
  requires L.is_list_ring_with pl head 1.0R (front @ back) **
    pure (pos == L.last_or head front)
  ensures exists* (v: N.struct_list_node).
    R.pts_to pos v **
    T.trade (R.pts_to pos v) (L.is_list_split_with pl head 1.0R pos (L.lnext v) front back)
{
  L.split_open pl head front back;
  with next. assert (L.is_list_split_with pl head 1.0R (L.last_or head front) next front back);
  unfold (L.is_list_split_with pl head 1.0R (L.last_or head front) next front back);
  with hv. assert (R.pts_to head hv);
  rewrite (L.is_list_seg_with pl (L.last_or head front) next head 1.0R back)
    as (L.is_list_seg_with pl pos next head 1.0R back);
  match front {
    Nil -> {
      unfold (L.is_list_seg_s_with pl head (L.lnext hv) next head 1.0R []);
      rewrite (R.pts_to head hv) as (R.pts_to pos hv);
      intro (T.trade (R.pts_to pos hv)
        (L.is_list_split_with pl head 1.0R pos (L.lnext hv) front back))
        #(L.is_list_seg_with pl pos next head 1.0R back)
      fn _ {
        rewrite (R.pts_to pos hv) as (R.pts_to head hv);
        fold (L.is_list_seg_s_with pl head (L.lnext hv) (L.lnext hv) head 1.0R []);
        rewrite (L.is_list_seg_with pl pos next head 1.0R back)
          as (L.is_list_seg_with pl pos (L.lnext hv) head 1.0R back);
        fold (L.is_list_split_with pl head 1.0R pos (L.lnext hv) front back);
      };
    }
    Cons f ft -> {
      L.last_or_flast head front;
      L.finit_flast_append front;
      rewrite (L.is_list_seg_s_with pl head (L.lnext hv) next head 1.0R front)
        as (L.is_list_seg_s_with pl head (L.lnext hv) next head 1.0R
          (L.finit front @ [L.flast front]));
      L.seg_s_peel_last pl head (L.lnext hv) next head (L.finit front) (L.flast front);
      with v. assert (R.pts_to (L.flast front) v);
      rewrite (R.pts_to (L.flast front) v) as (R.pts_to pos v);
      intro (T.trade (R.pts_to pos v)
        (L.is_list_split_with pl head 1.0R pos (L.lnext v) front back))
        #(R.pts_to head hv **
          L.is_list_seg_s_with pl head (L.lnext hv) (L.flast front) head 1.0R (L.finit front) **
          pl (L.flast front) ** L.is_list_seg_with pl pos next head 1.0R back)
      fn _ {
        rewrite (R.pts_to pos v) as (R.pts_to (L.flast front) v);
        if (Nil? back) {
          rewrite (L.is_list_seg_with pl pos next head 1.0R back)
            as (L.is_list_seg_with pl pos next head 1.0R []);
          L.seg_nil_elim pl pos next head 1.0R;
          rewrite (R.pts_to head hv) as (R.pts_to (L.lnext v) hv);
          L.seg_s_snoc pl head (L.lnext hv) head (L.finit front) (L.flast front);
          rewrite (R.pts_to (L.lnext v) hv) as (R.pts_to head hv);
          L.seg_nil_intro pl pos next head 1.0R;
          rewrite (L.is_list_seg_with pl pos next head 1.0R [])
            as (L.is_list_seg_with pl pos next head 1.0R back);
          rewrite (L.is_list_seg_s_with pl head (L.lnext hv) (L.lnext v) head 1.0R
            (L.finit front @ [L.flast front]))
            as (L.is_list_seg_s_with pl head (L.lnext hv) (L.lnext v) head 1.0R front);
          rewrite (L.is_list_seg_with pl pos next head 1.0R back)
            as (L.is_list_seg_with pl pos (L.lnext v) head 1.0R back);
          fold (L.is_list_split_with pl head 1.0R pos (L.lnext v) front back);
        } else {
          let b = Cons?.hd back;
          let bt = Cons?.tl back;
          rewrite (L.is_list_seg_with pl pos next head 1.0R back)
            as (L.is_list_seg_with pl pos next head 1.0R (b::bt));
          L.seg_cons_elim pl pos next head 1.0R b bt;
          with nv. assert (R.pts_to next nv);
          rewrite (R.pts_to next nv) as (R.pts_to (L.lnext v) nv);
          L.seg_s_snoc pl head (L.lnext hv) head (L.finit front) (L.flast front);
          rewrite (R.pts_to (L.lnext v) nv) as (R.pts_to next nv);
          L.seg_cons_intro pl pos next head 1.0R b bt;
          rewrite (L.is_list_seg_with pl pos next head 1.0R (b::bt))
            as (L.is_list_seg_with pl pos next head 1.0R back);
          rewrite (L.is_list_seg_s_with pl head (L.lnext hv) (L.lnext v) head 1.0R
            (L.finit front @ [L.flast front]))
            as (L.is_list_seg_s_with pl head (L.lnext hv) (L.lnext v) head 1.0R front);
          rewrite (L.is_list_seg_with pl pos next head 1.0R back)
            as (L.is_list_seg_with pl pos (L.lnext v) head 1.0R back);
          fold (L.is_list_split_with pl head 1.0R pos (L.lnext v) front back);
        }
      };
    }
  }
}

ghost
fn position_close (pl: L.payload) (head pos next: L.lref) (front back: list L.lref)
  (#v: N.struct_list_node)
  requires R.pts_to pos v **
    T.trade (R.pts_to pos v) (L.is_list_split_with pl head 1.0R pos (L.lnext v) front back) **
    pure (next == L.lnext v)
  ensures L.is_list_split_with pl head 1.0R pos next front back
{
  T.elim_trade (R.pts_to pos v) (L.is_list_split_with pl head 1.0R pos (L.lnext v) front back);
  rewrite (L.is_list_split_with pl head 1.0R pos (L.lnext v) front back)
    as (L.is_list_split_with pl head 1.0R pos next front back);
}

ghost
fn insert_head_prepare (pl: L.payload) (head: L.lref) (cells: list L.lref)
  requires L.is_list_ring_with pl head 1.0R cells
  ensures L.is_list_ring_with pl head 1.0R ([] @ cells)
{
  rewrite (L.is_list_ring_with pl head 1.0R cells)
    as (L.is_list_ring_with pl head 1.0R ([] @ cells));
}

ghost
fn insert_tail_prepare (pl: L.payload) (head: L.lref) (cells: list L.lref)
  requires L.is_list_ring_with pl head 1.0R cells
  ensures L.is_list_ring_with pl head 1.0R (cells @ [])
{
  FStar.List.Tot.Properties.append_l_nil cells;
  rewrite (L.is_list_ring_with pl head 1.0R cells)
    as (L.is_list_ring_with pl head 1.0R (cells @ []));
}

ghost
fn remove_head_prepare (pl: L.payload) (head first: L.lref) (cells: list L.lref)
  requires L.is_list_ring_with pl head 1.0R cells **
    pure (Cons? cells /\ first == L.first_or head cells)
  ensures L.is_list_ring_with pl head 1.0R ([] @ (first :: rest cells))
{
  rewrite (L.is_list_ring_with pl head 1.0R cells)
    as (L.is_list_ring_with pl head 1.0R ([] @ (first :: rest cells)));
}

ghost
fn move_empty (pl: L.payload) (source destination: L.lref) (src dst: list L.lref)
  requires L.is_list_ring_with pl source 1.0R src **
    L.is_list_ring_with pl destination 1.0R dst ** pure (src == [])
  ensures L.is_list_ring_with pl source 1.0R [] **
    L.is_list_ring_with pl destination 1.0R (dst @ src)
{
  FStar.List.Tot.Properties.append_l_nil dst;
  rewrite (L.is_list_ring_with pl source 1.0R src) as (L.is_list_ring_with pl source 1.0R []);
  rewrite (L.is_list_ring_with pl destination 1.0R dst)
    as (L.is_list_ring_with pl destination 1.0R (dst @ src));
}

let nonempty_ring (pl: L.payload) (head: L.lref) (cells: list L.lref) : slprop =
  L.is_list_ring_with pl head 1.0R cells ** pure (Cons? cells)

ghost
fn nonempty_intro (pl: L.payload) (head: L.lref) (cells: list L.lref)
  requires L.is_list_ring_with pl head 1.0R cells ** pure (cells =!= [])
  ensures nonempty_ring pl head cells
{
  fold (nonempty_ring pl head cells);
}

ghost
fn nonempty_elim (pl: L.payload) (head: L.lref) (cells: list L.lref)
  requires nonempty_ring pl head cells
  ensures L.is_list_ring_with pl head 1.0R cells ** pure (Cons? cells)
{
  unfold (nonempty_ring pl head cells);
}

let destination_rest (pl: L.payload) (destination tail: L.lref)
  (dst: list L.lref) (tp: L.lref) : slprop =
  match dst with
  | [] -> pure (tail == destination /\ tp == destination)
  | _::_ ->
    exists* (dv: N.struct_list_node).
      R.pts_to destination dv **
      chain pl destination (L.lnext dv) tail (L.finit dst) ** pl tail **
      pure (tail == L.flast dst /\ L.lprev dv == tail /\
        tp == L.last_or destination (L.finit dst))

let destination_prefix (pl: L.payload) (destination tail first: L.lref)
  (dst: list L.lref) : slprop =
  exists* (dv: N.struct_list_node).
    R.pts_to destination dv **
    chain pl destination (L.lnext dv) first dst **
    pure (tail == L.last_or destination dst /\ L.lprev dv == tail)

let move_rest0 (pl: L.payload) (source destination first last tail: L.lref)
  (src dst: list L.lref) (tp: L.lref) : slprop =
  L.is_list_ring_with pl source 1.0R src **
  destination_rest pl destination tail dst tp **
  pure (Cons? src /\ first == L.first_or source src /\ last == L.last_or source src)

ghost
fn move_open (pl: L.payload) (source destination first last tail: L.lref)
  (src dst: list L.lref)
  requires
    L.is_list_ring_with pl source 1.0R src **
    L.is_list_ring_with pl destination 1.0R dst **
    pure (Cons? src /\ first == L.first_or source src /\
      last == L.last_or source src /\ tail == L.last_or destination dst)
  ensures exists* (tv: N.struct_list_node).
    R.pts_to tail tv **
    move_rest0 pl source destination first last tail src dst (L.lprev tv) **
    pure (L.lnext tv == destination)
{
  ring_chain_out pl destination dst;
  with dv. assert (R.pts_to destination dv);
  match dst {
    Nil -> {
      unfold (chain pl destination (L.lnext dv) destination []);
      rewrite (R.pts_to destination dv) as (R.pts_to tail dv);
      fold (destination_rest pl destination tail [] (L.lprev dv));
      fold (move_rest0 pl source destination first last tail src dst (L.lprev dv));
    }
    Cons d dt -> {
      L.last_or_flast destination dst;
      chain_peel pl destination (L.lnext dv) destination dst;
      with tv. assert (R.pts_to (L.flast dst) tv);
      rewrite (R.pts_to (L.flast dst) tv) as (R.pts_to tail tv);
      rewrite (pl (L.flast dst)) as (pl tail);
      rewrite (chain pl destination (L.lnext dv) (L.flast dst) (L.finit dst))
        as (chain pl destination (L.lnext dv) tail (L.finit dst));
      fold (destination_rest pl destination tail dst (L.lprev tv));
      fold (move_rest0 pl source destination first last tail src dst (L.lprev tv));
    }
  }
}

ghost
fn destination_extend (pl: L.payload) (destination tail first: L.lref)
  (dst: list L.lref) (#tp: L.lref) (#tv: N.struct_list_node)
  requires R.pts_to tail tv ** destination_rest pl destination tail dst tp **
    pure (L.lnext tv == first /\ L.lprev tv == tp)
  ensures destination_prefix pl destination tail first dst
{
  match dst {
    Nil -> {
      unfold (destination_rest pl destination tail [] tp);
      rewrite (R.pts_to tail tv) as (R.pts_to destination tv);
      fold (chain pl destination (L.lnext tv) first []);
      fold (destination_prefix pl destination tail first dst);
    }
    Cons d dt -> {
      unfold (destination_rest pl destination tail dst tp);
      with dv. assert (R.pts_to destination dv);
      chain_snoc pl destination (L.lnext dv) first tail (L.finit dst);
      L.finit_flast_append dst;
      L.last_or_flast destination dst;
      rewrite (chain pl destination (L.lnext dv) first (L.finit dst @ [tail]))
        as (chain pl destination (L.lnext dv) first dst);
      fold (destination_prefix pl destination tail first dst);
    }
  }
}

let move_rest1 (pl: L.payload) (source destination first last tail: L.lref)
  (src dst: list L.lref) (nx: L.lref) : slprop =
  (exists* (sv: N.struct_list_node). R.pts_to source sv) **
  destination_prefix pl destination tail first dst **
  pl first ** chain pl first nx source (rest src) **
  pure (Cons? src /\ first == L.first_or source src /\ last == L.last_or source src)

ghost
fn move_first (pl: L.payload) (source destination first last tail: L.lref)
  (src dst: list L.lref) (#tp: L.lref) (#tv: N.struct_list_node)
  requires R.pts_to tail tv **
    move_rest0 pl source destination first last tail src dst tp **
    pure (L.lnext tv == first /\ L.lprev tv == tp)
  ensures exists* (fv: N.struct_list_node).
    R.pts_to first fv ** move_rest1 pl source destination first last tail src dst (L.lnext fv) **
    pure (L.lprev fv == source)
{
  unfold (move_rest0 pl source destination first last tail src dst tp);
  destination_extend pl destination tail first dst;
  ring_chain_out pl source src;
  with sv. assert (R.pts_to source sv);
  rewrite (chain pl source (L.lnext sv) source src)
    as (chain pl source (L.lnext sv) source (first::rest src));
  unfold (chain pl source (L.lnext sv) source (first::rest src));
  with fv. assert (R.pts_to (L.lnext sv) fv);
  rewrite (R.pts_to (L.lnext sv) fv) as (R.pts_to first fv);
  rewrite (pl (L.lnext sv)) as (pl first);
  rewrite (chain pl (L.lnext sv) (L.lnext fv) source (rest src))
    as (chain pl first (L.lnext fv) source (rest src));
  fold (move_rest1 pl source destination first last tail src dst (L.lnext fv));
}

let move_rest2 (pl: L.payload) (source destination first last tail: L.lref)
  (src dst: list L.lref) (lp: L.lref) : slprop =
  (exists* (sv: N.struct_list_node). R.pts_to source sv) **
  destination_prefix pl destination tail first dst **
  chain pl tail first last (initial src) ** pl last **
  pure (Cons? src /\ last == final src /\ lp == L.last_or tail (initial src))

ghost
fn move_last (pl: L.payload) (source destination first last tail: L.lref)
  (src dst: list L.lref) (#nx: L.lref) (#fv: N.struct_list_node)
  requires R.pts_to first fv **
    move_rest1 pl source destination first last tail src dst nx **
    pure (L.lnext fv == nx /\ L.lprev fv == tail)
  ensures exists* (lv: N.struct_list_node).
    R.pts_to last lv ** move_rest2 pl source destination first last tail src dst (L.lprev lv) **
    pure (L.lnext lv == source)
{
  unfold (move_rest1 pl source destination first last tail src dst nx);
  rewrite (chain pl first nx source (rest src))
    as (chain pl first (L.lnext fv) source (rest src));
  fold (chain pl tail first source (first::rest src));
  rewrite (chain pl tail first source (first::rest src))
    as (chain pl tail first source src);
  chain_peel pl tail first source src;
  L.last_or_flast source src;
  with lv. assert (R.pts_to (L.flast src) lv);
  rewrite (R.pts_to (L.flast src) lv) as (R.pts_to last lv);
  rewrite (pl (L.flast src)) as (pl last);
  rewrite (chain pl tail first (L.flast src) (L.finit src))
    as (chain pl tail first last (initial src));
  fold (move_rest2 pl source destination first last tail src dst (L.lprev lv));
}

let move_rest3 (pl: L.payload) (source destination first last tail: L.lref)
  (src dst: list L.lref) (dn: L.lref) : slprop =
  (exists* (sv: N.struct_list_node). R.pts_to source sv) **
  chain pl destination dn first dst ** chain pl tail first destination src **
  pure (Cons? src /\ last == final src /\ tail == L.last_or destination dst)

ghost
fn move_destination (pl: L.payload) (source destination first last tail: L.lref)
  (src dst: list L.lref) (#lp: L.lref) (#lv: N.struct_list_node)
  requires R.pts_to last lv **
    move_rest2 pl source destination first last tail src dst lp **
    pure (L.lnext lv == destination /\ L.lprev lv == lp)
  ensures exists* (dv: N.struct_list_node).
    R.pts_to destination dv **
    move_rest3 pl source destination first last tail src dst (L.lnext dv)
{
  unfold (move_rest2 pl source destination first last tail src dst lp);
  rewrite (chain pl tail first last (initial src))
    as (chain pl tail first last (L.finit src));
  chain_snoc pl tail first destination last (L.finit src);
  L.finit_flast_append src;
  rewrite (chain pl tail first destination (L.finit src @ [last]))
    as (chain pl tail first destination src);
  unfold (destination_prefix pl destination tail first dst);
  with dv. assert (R.pts_to destination dv);
  fold (move_rest3 pl source destination first last tail src dst (L.lnext dv));
}

ghost
fn move_close (pl: L.payload) (source destination first last tail: L.lref)
  (src dst: list L.lref) (#dn: L.lref) (#dv: N.struct_list_node)
  requires R.pts_to destination dv **
    move_rest3 pl source destination first last tail src dst dn **
    pure (L.lnext dv == dn /\ L.lprev dv == last)
  ensures R.pts_to_uninit source ** L.is_list_ring_with pl destination 1.0R (dst @ src)
{
  unfold (move_rest3 pl source destination first last tail src dst dn);
  rewrite (chain pl destination dn first dst)
    as (chain pl destination (L.lnext dv) first dst);
  rewrite (chain pl tail first destination src)
    as (chain pl (L.last_or destination dst) first destination src);
  chain_join pl destination (L.lnext dv) first destination dst src;
  L.last_or_append_cons destination dst src;
  L.last_or_flast destination src;
  ring_chain_in pl destination (dst @ src);
}

ghost
fn indexed_move_finish (#a: Type0) (pl: L.ipayload a) (source destination: L.lref)
                       (src dst: list (L.lref & a))
  requires L.is_list_ring_with L.emp_pl source 1.0R [] **
    L.is_list_ring_with L.emp_pl destination 1.0R (L.cells_of dst @ L.cells_of src) **
    L.ipayload_of pl src ** L.ipayload_of pl dst
  ensures L.is_list_ring_ix pl source 1.0R [] **
    L.is_list_ring_ix pl destination 1.0R (dst @ src)
{
  L.ipayload_of_join pl dst src;
  L.cells_of_append dst src;
  rewrite (L.is_list_ring_with L.emp_pl destination 1.0R
    (L.cells_of dst @ L.cells_of src))
    as (L.is_list_ring_with L.emp_pl destination 1.0R (L.cells_of (dst @ src)));
  fold (L.ipayload_of pl []);
  rewrite (L.is_list_ring_with L.emp_pl source 1.0R [])
    as (L.is_list_ring_with L.emp_pl source 1.0R (L.cells_of #a []));
  L.ring_ix_close pl source 1.0R [];
  L.ring_ix_close pl destination 1.0R (dst @ src);
}

ghost
fn indexed_init (#a: Type0) (pl: L.ipayload a) (head: L.lref)
  requires L.is_list_ring head 1.0R []
  ensures L.is_list_ring_ix pl head 1.0R []
{
  fold (L.ipayload_of pl []);
  L.ring_ix_in pl head 1.0R [];
}

ghost
fn indexed_normalize (#a: Type0) (pl: L.ipayload a) (head: L.lref)
                     (es: list (L.lref & a)) (#old_es: list (L.lref & a))
  requires L.is_list_ring_ix pl head 1.0R old_es ** pure (old_es == es)
  ensures L.is_list_ring_ix pl head 1.0R es
{
  rewrite (L.is_list_ring_ix pl head 1.0R old_es)
    as (L.is_list_ring_ix pl head 1.0R es);
}

ghost
fn indexed_release_empty (#a: Type0) (pl: L.ipayload a) (head: L.lref)
  requires L.is_list_ring_ix pl head 1.0R []
  ensures exists* (v: N.struct_list_node). R.pts_to head v
{
  L.ring_ix_open pl head 1.0R [];
  unfold (L.ipayload_of pl []);
  L.ring_elim_empty L.emp_pl head;
}
