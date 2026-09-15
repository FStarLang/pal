module IntrusiveListValidate
open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module R = Pulse.Lib.Reference
module N = Struct_list_node
module L = IntrusiveList
module T = Pulse.Lib.Trade

unfold let quarter : perm = 0.25R

let fields (node: L.lref) (v: N.struct_list_node) : slprop =
  N.struct_list_node__aux_raw_unfolded node quarter **
  R.pts_to (N.struct_list_node__next_1 node) #quarter (L.lnext v) **
  R.pts_to (N.struct_list_node__prev_1 node) #quarter (L.lprev v)

ghost
fn rec seg_share (prev cur endl: L.lref) (p: perm) (cells: list L.lref)
  requires L.is_list_seg prev cur endl p cells
  ensures L.is_list_seg prev cur endl (p /. 2.0R) cells **
    L.is_list_seg prev cur endl (p /. 2.0R) cells
  decreases cells
{
  match cells {
    Nil -> {
      L.seg_nil_elim L.no_payload prev cur endl p;
      L.seg_nil_intro L.no_payload prev cur endl (p /. 2.0R);
      L.seg_nil_intro L.no_payload prev cur endl (p /. 2.0R);
    }
    Cons hd tl -> {
      L.seg_cons_elim L.no_payload prev cur endl p hd tl;
      with v. assert (R.pts_to cur #p v);
      R.share cur;
      seg_share cur (L.lnext v) endl p tl;
      L.seg_cons_intro L.no_payload prev cur endl (p /. 2.0R) hd tl;
      L.seg_cons_intro L.no_payload prev cur endl (p /. 2.0R) hd tl;
    }
  }
}

let held (r: L.lref) (p: perm) (v: N.struct_list_node) = R.pts_to r #p v

[@@allow_ambiguous]
ghost
fn rec seg_gather (prev cur endl: L.lref) (p: perm { p <=. 0.5R })
                  (cells: list L.lref)
  requires L.is_list_seg prev cur endl p cells **
    L.is_list_seg prev cur endl p cells
  ensures L.is_list_seg prev cur endl (p +. p) cells
  decreases cells
{
  match cells {
    Nil -> {
      L.seg_nil_elim L.no_payload prev cur endl p;
      L.seg_nil_elim L.no_payload prev cur endl p;
      L.seg_nil_intro L.no_payload prev cur endl (p +. p);
    }
    Cons hd tl -> {
      L.seg_cons_elim L.no_payload prev cur endl p hd tl;
      with v1. assert (R.pts_to cur #p v1);
      fold (held cur p v1);
      L.seg_cons_elim L.no_payload prev cur endl p hd tl;
      with v2. assert (R.pts_to cur #p v2);
      unfold (held cur p v1);
      R.gather cur #(hide v1) #(hide v2) #p #p;
      rewrite (L.is_list_seg cur (L.lnext v2) endl p tl)
        as (L.is_list_seg cur (L.lnext v1) endl p tl);
      seg_gather cur (L.lnext v1) endl p tl;
      L.seg_cons_intro L.no_payload prev cur endl (p +. p) hd tl;
    }
  }
}

ghost
fn ring_share (head: L.lref) (p: perm) (cells: list L.lref)
  requires L.is_list_ring head p cells
  ensures L.is_list_ring head (p /. 2.0R) cells **
    L.is_list_ring head (p /. 2.0R) cells
{
  L.ring_unfold L.no_payload head;
  with hv. assert (R.pts_to head #p hv);
  R.share head;
  seg_share head (L.lnext hv) head p cells;
  L.ring_fold L.no_payload head;
  L.ring_fold L.no_payload head;
}

[@@allow_ambiguous]
ghost
fn ring_gather (head: L.lref) (p: perm { p <=. 0.5R }) (cells: list L.lref)
  requires L.is_list_ring head p cells ** L.is_list_ring head p cells
  ensures L.is_list_ring head (p +. p) cells
{
  L.ring_unfold L.no_payload head;
  with hv1. assert (R.pts_to head #p hv1);
  fold (held head p hv1);
  L.ring_unfold L.no_payload head;
  with hv2. assert (R.pts_to head #p hv2);
  unfold (held head p hv1);
  R.gather head #(hide hv1) #(hide hv2) #p #p;
  rewrite (L.is_list_seg head (L.lnext hv2) head p cells)
    as (L.is_list_seg head (L.lnext hv1) head p cells);
  seg_gather head (L.lnext hv1) head p cells;
  L.ring_fold L.no_payload head;
}

let last_or_step (d hd: L.lref) (tl: list L.lref)
  : Lemma (L.last_or d (hd :: tl) == L.last_or hd tl)
  = match tl with
    | [] -> ()
    | _ :: _ -> L.last_or_indep d hd tl

ghost
fn rec seg_borrow (prev cur endl: L.lref) (p: perm)
                  (front: list L.lref) (node: L.lref) (back: list L.lref)
  requires L.is_list_seg prev cur endl p (front @ (node :: back))
  ensures
    R.pts_to node #p (L.mklink (L.first_or endl back) (L.last_or prev front)) **
    T.trade
      (R.pts_to node #p (L.mklink (L.first_or endl back) (L.last_or prev front)))
      (L.is_list_seg prev cur endl p (front @ (node :: back)))
  decreases front
{
  match front {
    Nil -> {
      L.seg_cons_elim L.no_payload prev cur endl p node back;
      with v. assert (R.pts_to cur #p v);
      L.seg_first L.no_payload cur (L.lnext v) endl;
      rewrite (R.pts_to cur #p v)
        as (R.pts_to node #p (L.mklink (L.first_or endl back) prev));
      intro (T.trade
        (R.pts_to node #p (L.mklink (L.first_or endl back) prev))
        (L.is_list_seg prev cur endl p (front @ (node :: back))))
        #(L.is_list_seg cur (L.lnext v) endl p back)
      fn _ {
        rewrite (R.pts_to node #p (L.mklink (L.first_or endl back) prev))
          as (R.pts_to cur #p v);
        L.seg_cons_intro L.no_payload prev cur endl p node back;
      };
    }
    Cons hd tl -> {
      L.seg_cons_elim L.no_payload prev cur endl p hd (tl @ (node :: back));
      with v. assert (R.pts_to cur #p v);
      seg_borrow cur (L.lnext v) endl p tl node back;
      last_or_step prev hd tl;
      let nv = L.mklink (L.first_or endl back) (L.last_or prev front);
      rewrite (R.pts_to node #p (L.mklink (L.first_or endl back) (L.last_or cur tl)))
        as (R.pts_to node #p nv);
      intro (T.trade (R.pts_to node #p nv)
        (L.is_list_seg prev cur endl p (front @ (node :: back))))
        #(R.pts_to cur #p v **
          T.trade
            (R.pts_to node #p (L.mklink (L.first_or endl back) (L.last_or cur tl)))
            (L.is_list_seg cur (L.lnext v) endl p (tl @ (node :: back))))
      fn _ {
        rewrite (R.pts_to node #p nv)
          as (R.pts_to node #p (L.mklink (L.first_or endl back) (L.last_or cur tl)));
        T.elim_trade
          (R.pts_to node #p (L.mklink (L.first_or endl back) (L.last_or cur tl)))
          (L.is_list_seg cur (L.lnext v) endl p (tl @ (node :: back)));
        L.seg_cons_intro L.no_payload prev cur endl p hd (tl @ (node :: back));
      };
    }
  }
}

ghost
fn borrow_head (head: L.lref) (p: perm) (cells: list L.lref)
  requires L.is_list_ring head p cells
  ensures
    R.pts_to head #p (L.mklink (L.first_or head cells) (L.last_or head cells)) **
    T.trade
      (R.pts_to head #p (L.mklink (L.first_or head cells) (L.last_or head cells)))
      (L.is_list_ring head p cells)
{
  L.ring_open_full L.no_payload head;
  with hv. assert (R.pts_to head #p hv);
  let v = L.mklink (L.first_or head cells) (L.last_or head cells);
  rewrite (R.pts_to head #p hv) as (R.pts_to head #p v);
  intro (T.trade (R.pts_to head #p v) (L.is_list_ring head p cells))
    #(L.is_list_seg head (L.lnext hv) head p cells)
  fn _ {
    rewrite (R.pts_to head #p v) as (R.pts_to head #p hv);
    L.ring_close L.no_payload head;
  };
}

ghost
fn borrow_member (head: L.lref) (p: perm)
                 (front: list L.lref) (node: L.lref) (back: list L.lref)
  requires L.is_list_ring head p (front @ (node :: back))
  ensures
    R.pts_to node #p (L.mklink (L.first_or head back) (L.last_or head front)) **
    T.trade
      (R.pts_to node #p (L.mklink (L.first_or head back) (L.last_or head front)))
      (L.is_list_ring head p (front @ (node :: back)))
{
  L.ring_unfold L.no_payload head;
  with hv. assert (R.pts_to head #p hv);
  seg_borrow head (L.lnext hv) head p front node back;
  let v = L.mklink (L.first_or head back) (L.last_or head front);
  intro (T.trade (R.pts_to node #p v)
    (L.is_list_ring head p (front @ (node :: back))))
    #(R.pts_to head #p hv **
      T.trade (R.pts_to node #p v)
        (L.is_list_seg head (L.lnext hv) head p (front @ (node :: back))))
  fn _ {
    T.elim_trade (R.pts_to node #p v)
      (L.is_list_seg head (L.lnext hv) head p (front @ (node :: back)));
    L.ring_fold L.no_payload head;
  };
}

ghost
fn borrow_successor (head: L.lref) (p: perm)
                    (front: list L.lref) (node: L.lref) (back: list L.lref)
  requires L.is_list_ring head p (front @ (node :: back))
  ensures exists* (v: N.struct_list_node).
    R.pts_to (L.first_or head back) #p v **
    pure (L.lprev v == node) **
    T.trade (R.pts_to (L.first_or head back) #p v)
      (L.is_list_ring head p (front @ (node :: back)))
{
  match back {
    Nil -> {
      L.last_or_snoc head front node;
      borrow_head head p (front @ [node]);
    }
    Cons hd tl -> {
      FStar.List.Tot.Properties.append_assoc front [node] (hd :: tl);
      L.last_or_snoc head front node;
      rewrite (L.is_list_ring head p (front @ (node :: back)))
        as (L.is_list_ring head p ((front @ [node]) @ (hd :: tl)));
      borrow_member head p (front @ [node]) hd tl;
      let v = L.mklink (L.first_or head tl) (L.last_or head (front @ [node]));
      rewrite (T.trade (R.pts_to hd #p v)
        (L.is_list_ring head p ((front @ [node]) @ (hd :: tl))))
        as (T.trade (R.pts_to (L.first_or head back) #p v)
          (L.is_list_ring head p (front @ (node :: back))));
    }
  }
}

ghost
fn borrow_predecessor (head: L.lref) (p: perm)
                      (front: list L.lref) (node: L.lref) (back: list L.lref)
  requires L.is_list_ring head p (front @ (node :: back))
  ensures exists* (v: N.struct_list_node).
    R.pts_to (L.last_or head front) #p v **
    pure (L.lnext v == node) **
    T.trade (R.pts_to (L.last_or head front) #p v)
      (L.is_list_ring head p (front @ (node :: back)))
{
  match front {
    Nil -> {
      borrow_head head p (node :: back);
    }
    Cons hd tl -> {
      L.finit_flast_append front;
      L.last_or_flast head front;
      FStar.List.Tot.Properties.append_assoc (L.finit front) [L.flast front]
        (node :: back);
      rewrite (L.is_list_ring head p (front @ (node :: back)))
        as (L.is_list_ring head p (L.finit front @ (L.flast front :: node :: back)));
      borrow_member head p (L.finit front) (L.flast front) (node :: back);
      let v = L.mklink node (L.last_or head (L.finit front));
      rewrite (R.pts_to (L.flast front) #p v)
        as (R.pts_to (L.last_or head front) #p v);
      rewrite (T.trade (R.pts_to (L.flast front) #p v)
        (L.is_list_ring head p (L.finit front @ (L.flast front :: node :: back))))
        as (T.trade (R.pts_to (L.last_or head front) #p v)
          (L.is_list_ring head p (front @ (node :: back))));
    }
  }
}

noeq type witness = {
  focus_value: N.struct_list_node;
  next_value: N.struct_list_node;
  prev_value: N.struct_list_node;
}

(* Each snapshot owns one quarter, so even three aliases use only three
   quarters of a cell. The witness fixes the values returned to the lender. *)
let view (node: L.lref) (w: witness) : slprop =
  R.pts_to node #quarter w.focus_value **
  R.pts_to (L.lnext w.focus_value) #quarter w.next_value **
  R.pts_to (L.lprev w.focus_value) #quarter w.prev_value **
  pure (L.lprev w.next_value == node /\ L.lnext w.prev_value == node)

ghost
fn view_open_focus (node: L.lref) (#w: witness)
  requires view node w
  ensures fields node w.focus_value **
    T.trade (fields node w.focus_value) (view node w)
{
  unfold (view node w);
  N.struct_list_node__aux_raw_unfold node w.focus_value;
  fold (fields node w.focus_value);
  intro (T.trade (fields node w.focus_value) (view node w))
    #(R.pts_to (L.lnext w.focus_value) #quarter w.next_value **
      R.pts_to (L.lprev w.focus_value) #quarter w.prev_value)
  fn _ {
    unfold (fields node w.focus_value);
    N.struct_list_node__aux_raw_fold node (L.lnext w.focus_value) (L.lprev w.focus_value);
    fold (view node w);
  };
}

ghost
fn view_open_next (node next: L.lref) (#w: witness)
  requires view node w ** pure (next == L.lnext w.focus_value)
  ensures fields next w.next_value **
    pure (L.lprev w.next_value == node) **
    T.trade (fields next w.next_value) (view node w)
{
  unfold (view node w);
  rewrite (R.pts_to (L.lnext w.focus_value) #quarter w.next_value)
    as (R.pts_to next #quarter w.next_value);
  N.struct_list_node__aux_raw_unfold next w.next_value;
  fold (fields next w.next_value);
  intro (T.trade (fields next w.next_value) (view node w))
    #(R.pts_to node #quarter w.focus_value **
      R.pts_to (L.lprev w.focus_value) #quarter w.prev_value)
  fn _ {
    unfold (fields next w.next_value);
    N.struct_list_node__aux_raw_fold next (L.lnext w.next_value) (L.lprev w.next_value);
    rewrite (R.pts_to next #quarter w.next_value)
      as (R.pts_to (L.lnext w.focus_value) #quarter w.next_value);
    fold (view node w);
  };
}

ghost
fn view_open_prev (node prev: L.lref) (#w: witness)
  requires view node w ** pure (prev == L.lprev w.focus_value)
  ensures fields prev w.prev_value **
    pure (L.lnext w.prev_value == node) **
    T.trade (fields prev w.prev_value) (view node w)
{
  unfold (view node w);
  rewrite (R.pts_to (L.lprev w.focus_value) #quarter w.prev_value)
    as (R.pts_to prev #quarter w.prev_value);
  N.struct_list_node__aux_raw_unfold prev w.prev_value;
  fold (fields prev w.prev_value);
  intro (T.trade (fields prev w.prev_value) (view node w))
    #(R.pts_to node #quarter w.focus_value **
      R.pts_to (L.lnext w.focus_value) #quarter w.next_value)
  fn _ {
    unfold (fields prev w.prev_value);
    N.struct_list_node__aux_raw_fold prev (L.lnext w.prev_value) (L.lprev w.prev_value);
    rewrite (R.pts_to prev #quarter w.prev_value)
      as (R.pts_to (L.lprev w.focus_value) #quarter w.prev_value);
    fold (view node w);
  };
}

ghost
fn view_close (node target: L.lref) (#w: witness) (#v: N.struct_list_node)
  requires fields target v ** T.trade (fields target v) (view node w)
  ensures view node w
{
  T.elim_trade (fields target v) (view node w);
}

ghost
fn fields_open (target: L.lref) (#v: N.struct_list_node)
  requires fields target v
  ensures
    N.struct_list_node__aux_raw_unfolded target quarter **
    R.pts_to (N.struct_list_node__next_1 target) #quarter (L.lnext v) **
    R.pts_to (N.struct_list_node__prev_1 target) #quarter (L.lprev v)
{
  unfold (fields target v);
}

ghost
fn fields_close (target: L.lref) (#v: N.struct_list_node)
  requires
    N.struct_list_node__aux_raw_unfolded target quarter **
    R.pts_to (N.struct_list_node__next_1 target) #quarter (L.lnext v) **
    R.pts_to (N.struct_list_node__prev_1 target) #quarter (L.lprev v)
  ensures fields target v
{
  fold (fields target v);
}

(* The fourth quarter and every payload stay in the restoration trade. *)
ghost
fn member_view (pl: L.payload) (head node: L.lref)
               (front back: list L.lref)
  requires L.is_list_ring_with pl head 1.0R (front @ (node :: back))
  ensures exists* (w: witness).
    view node w **
    T.trade (view node w)
      (L.is_list_ring_with pl head 1.0R (front @ (node :: back)))
{
  let cells = front @ (node :: back);
  rewrite (L.is_list_ring_with pl head 1.0R (front @ (node :: back)))
    as (L.is_list_ring_with pl head 1.0R cells);
  L.ring_pl_out pl head 1.0R cells;
  ring_share head 1.0R cells;
  rewrite (L.is_list_ring head (1.0R /. 2.0R) cells)
    as (L.is_list_ring head 0.5R cells);
  rewrite (L.is_list_ring head (1.0R /. 2.0R) cells)
    as (L.is_list_ring head 0.5R cells);
  ring_share head 0.5R cells;
  ring_share head 0.5R cells;
  rewrite (L.is_list_ring head (0.5R /. 2.0R) cells)
    as (L.is_list_ring head quarter cells);
  rewrite (L.is_list_ring head (0.5R /. 2.0R) cells)
    as (L.is_list_ring head quarter cells);
  rewrite (L.is_list_ring head (0.5R /. 2.0R) cells)
    as (L.is_list_ring head quarter cells);
  rewrite (L.is_list_ring head (0.5R /. 2.0R) cells)
    as (L.is_list_ring head quarter cells);
  rewrite (L.is_list_ring head quarter cells)
    as (L.is_list_ring head quarter (front @ (node :: back)));
  borrow_member head quarter front node back;
  rewrite (L.is_list_ring head quarter cells)
    as (L.is_list_ring head quarter (front @ (node :: back)));
  borrow_successor head quarter front node back;
  with nv. assert (R.pts_to (L.first_or head back) #quarter nv);
  rewrite (L.is_list_ring head quarter cells)
    as (L.is_list_ring head quarter (front @ (node :: back)));
  borrow_predecessor head quarter front node back;
  with pv. assert (R.pts_to (L.last_or head front) #quarter pv);
  let v = L.mklink (L.first_or head back) (L.last_or head front);
  let w = { focus_value = v; next_value = nv; prev_value = pv };
  rewrite (R.pts_to (L.first_or head back) #quarter nv)
    as (R.pts_to (L.lnext w.focus_value) #quarter w.next_value);
  rewrite (R.pts_to (L.last_or head front) #quarter pv)
    as (R.pts_to (L.lprev w.focus_value) #quarter w.prev_value);
  fold (view node w);
  rewrite (T.trade
    (R.pts_to node #quarter (L.mklink (L.first_or head back) (L.last_or head front)))
    (L.is_list_ring head quarter (front @ (node :: back))))
    as (T.trade (R.pts_to node #quarter v) (L.is_list_ring head quarter cells));
  rewrite (T.trade (R.pts_to (L.first_or head back) #quarter nv)
    (L.is_list_ring head quarter (front @ (node :: back))))
    as (T.trade (R.pts_to (L.first_or head back) #quarter nv)
      (L.is_list_ring head quarter cells));
  rewrite (T.trade (R.pts_to (L.last_or head front) #quarter pv)
    (L.is_list_ring head quarter (front @ (node :: back))))
    as (T.trade (R.pts_to (L.last_or head front) #quarter pv)
      (L.is_list_ring head quarter cells));
  intro (T.trade (view node w) (L.is_list_ring_with pl head 1.0R cells))
    #(T.trade (R.pts_to node #quarter v) (L.is_list_ring head quarter cells) **
      T.trade (R.pts_to (L.first_or head back) #quarter nv)
        (L.is_list_ring head quarter cells) **
      T.trade (R.pts_to (L.last_or head front) #quarter pv)
        (L.is_list_ring head quarter cells) **
      L.is_list_ring head quarter cells ** L.payload_of pl cells)
  fn _ {
    unfold (view node w);
    rewrite (R.pts_to (L.lnext w.focus_value) #quarter w.next_value)
      as (R.pts_to (L.first_or head back) #quarter nv);
    rewrite (R.pts_to (L.lprev w.focus_value) #quarter w.prev_value)
      as (R.pts_to (L.last_or head front) #quarter pv);
    T.elim_trade (R.pts_to node #quarter v) (L.is_list_ring head quarter cells);
    T.elim_trade (R.pts_to (L.first_or head back) #quarter nv)
      (L.is_list_ring head quarter cells);
    T.elim_trade (R.pts_to (L.last_or head front) #quarter pv)
      (L.is_list_ring head quarter cells);
    ring_gather head quarter cells;
    ring_gather head quarter cells;
    rewrite (L.is_list_ring head (quarter +. quarter) cells)
      as (L.is_list_ring head 0.5R cells);
    rewrite (L.is_list_ring head (quarter +. quarter) cells)
      as (L.is_list_ring head 0.5R cells);
    ring_gather head 0.5R cells;
    rewrite (L.is_list_ring head (0.5R +. 0.5R) cells)
      as (L.is_list_ring head 1.0R cells);
    L.ring_pl_in pl head 1.0R cells;
  };
  rewrite (T.trade (view node w) (L.is_list_ring_with pl head 1.0R cells))
    as (T.trade (view node w)
      (L.is_list_ring_with pl head 1.0R (front @ (node :: back))));
}

ghost
fn borrow_first (head: L.lref) (p: perm) (cells: list L.lref)
  requires L.is_list_ring head p cells
  ensures exists* (v: N.struct_list_node).
    R.pts_to (L.first_or head cells) #p v **
    pure (L.lprev v == head) **
    T.trade (R.pts_to (L.first_or head cells) #p v)
      (L.is_list_ring head p cells)
{
  match cells {
    Nil -> { borrow_head head p cells; }
    Cons hd tl -> { borrow_member head p [] hd tl; }
  }
}

ghost
fn borrow_last (head: L.lref) (p: perm) (cells: list L.lref)
  requires L.is_list_ring head p cells
  ensures exists* (v: N.struct_list_node).
    R.pts_to (L.last_or head cells) #p v **
    pure (L.lnext v == head) **
    T.trade (R.pts_to (L.last_or head cells) #p v)
      (L.is_list_ring head p cells)
{
  match cells {
    Nil -> { borrow_head head p cells; }
    Cons hd tl -> {
      L.finit_flast_append cells;
      L.last_or_flast head cells;
      rewrite (L.is_list_ring head p cells)
        as (L.is_list_ring head p (L.finit cells @ [L.flast cells]));
      borrow_member head p (L.finit cells) (L.flast cells) [];
      let v = L.mklink head (L.last_or head (L.finit cells));
      rewrite (R.pts_to (L.flast cells) #p v)
        as (R.pts_to (L.last_or head cells) #p v);
      rewrite (T.trade (R.pts_to (L.flast cells) #p v)
        (L.is_list_ring head p (L.finit cells @ [L.flast cells])))
        as (T.trade (R.pts_to (L.last_or head cells) #p v)
          (L.is_list_ring head p cells));
    }
  }
}

ghost
fn sentinel_view (pl: L.payload) (head: L.lref) (cells: list L.lref)
  requires L.is_list_ring_with pl head 1.0R cells
  ensures exists* (w: witness).
    view head w **
    T.trade (view head w) (L.is_list_ring_with pl head 1.0R cells)
{
  L.ring_pl_out pl head 1.0R cells;
  ring_share head 1.0R cells;
  rewrite (L.is_list_ring head (1.0R /. 2.0R) cells)
    as (L.is_list_ring head 0.5R cells);
  rewrite (L.is_list_ring head (1.0R /. 2.0R) cells)
    as (L.is_list_ring head 0.5R cells);
  ring_share head 0.5R cells;
  ring_share head 0.5R cells;
  rewrite (L.is_list_ring head (0.5R /. 2.0R) cells)
    as (L.is_list_ring head quarter cells);
  rewrite (L.is_list_ring head (0.5R /. 2.0R) cells)
    as (L.is_list_ring head quarter cells);
  rewrite (L.is_list_ring head (0.5R /. 2.0R) cells)
    as (L.is_list_ring head quarter cells);
  rewrite (L.is_list_ring head (0.5R /. 2.0R) cells)
    as (L.is_list_ring head quarter cells);
  borrow_head head quarter cells;
  let v = L.mklink (L.first_or head cells) (L.last_or head cells);
  fold (held head quarter v);
  borrow_first head quarter cells;
  with nv. assert (R.pts_to (L.first_or head cells) #quarter nv);
  fold (held (L.first_or head cells) quarter nv);
  borrow_last head quarter cells;
  with pv. assert (R.pts_to (L.last_or head cells) #quarter pv);
  unfold (held head quarter v);
  unfold (held (L.first_or head cells) quarter nv);
  let w = { focus_value = v; next_value = nv; prev_value = pv };
  rewrite (R.pts_to (L.first_or head cells) #quarter nv)
    as (R.pts_to (L.lnext w.focus_value) #quarter w.next_value);
  rewrite (R.pts_to (L.last_or head cells) #quarter pv)
    as (R.pts_to (L.lprev w.focus_value) #quarter w.prev_value);
  fold (view head w);
  intro (T.trade (view head w) (L.is_list_ring_with pl head 1.0R cells))
    #(T.trade (R.pts_to head #quarter v) (L.is_list_ring head quarter cells) **
      T.trade (R.pts_to (L.first_or head cells) #quarter nv)
        (L.is_list_ring head quarter cells) **
      T.trade (R.pts_to (L.last_or head cells) #quarter pv)
        (L.is_list_ring head quarter cells) **
      L.is_list_ring head quarter cells ** L.payload_of pl cells)
  fn _ {
    unfold (view head w);
    rewrite (R.pts_to (L.lnext w.focus_value) #quarter w.next_value)
      as (R.pts_to (L.first_or head cells) #quarter nv);
    rewrite (R.pts_to (L.lprev w.focus_value) #quarter w.prev_value)
      as (R.pts_to (L.last_or head cells) #quarter pv);
    T.elim_trade (R.pts_to head #quarter v) (L.is_list_ring head quarter cells);
    T.elim_trade (R.pts_to (L.first_or head cells) #quarter nv)
      (L.is_list_ring head quarter cells);
    T.elim_trade (R.pts_to (L.last_or head cells) #quarter pv)
      (L.is_list_ring head quarter cells);
    ring_gather head quarter cells;
    ring_gather head quarter cells;
    rewrite (L.is_list_ring head (quarter +. quarter) cells)
      as (L.is_list_ring head 0.5R cells);
    rewrite (L.is_list_ring head (quarter +. quarter) cells)
      as (L.is_list_ring head 0.5R cells);
    ring_gather head 0.5R cells;
    rewrite (L.is_list_ring head (0.5R +. 0.5R) cells)
      as (L.is_list_ring head 1.0R cells);
    L.ring_pl_in pl head 1.0R cells;
  };
}

ghost
fn ring_view (pl: L.payload) (head node: L.lref) (front back: list L.lref)
  requires L.is_list_ring_with pl head 1.0R (front @ back) **
    pure (node == L.last_or head front)
  ensures exists* (w: witness).
    view node w **
    T.trade (view node w) (L.is_list_ring_with pl head 1.0R (front @ back))
{
  match front {
    Nil -> {
      rewrite (L.is_list_ring_with pl head 1.0R (front @ back))
        as (L.is_list_ring_with pl node 1.0R back);
      sentinel_view pl node back;
      with w. assert (view node w);
      rewrite (T.trade (view node w) (L.is_list_ring_with pl node 1.0R back))
        as (T.trade (view node w) (L.is_list_ring_with pl head 1.0R (front @ back)));
    }
    Cons hd tl -> {
      L.finit_flast_append front;
      L.last_or_flast head front;
      FStar.List.Tot.Properties.append_assoc (L.finit front) [L.flast front] back;
      rewrite (L.is_list_ring_with pl head 1.0R (front @ back))
        as (L.is_list_ring_with pl head 1.0R (L.finit front @ (node :: back)));
      member_view pl head node (L.finit front) back;
      with w. assert (view node w);
      rewrite (T.trade (view node w)
        (L.is_list_ring_with pl head 1.0R (L.finit front @ (node :: back))))
        as (T.trade (view node w) (L.is_list_ring_with pl head 1.0R (front @ back)));
    }
  }
}

ghost
fn restore_ring (pl: L.payload) (head node: L.lref) (cells: list L.lref)
                (#w: witness)
  requires view node w **
    T.trade (view node w) (L.is_list_ring_with pl head 1.0R cells)
  ensures L.is_list_ring_with pl head 1.0R cells
{
  T.elim_trade (view node w) (L.is_list_ring_with pl head 1.0R cells);
}

let all_fields (node: L.lref) (w: witness) =
  fields node w.focus_value **
  fields (L.lnext w.focus_value) w.next_value **
  fields (L.lprev w.focus_value) w.prev_value

(* Opening and closing are ghost-only. The actual assertion expressions,
   including their conditionally evaluated reads, need not be changed. *)
ghost
fn view_open_all (node: L.lref) (#w: witness)
  requires view node w
  ensures
    N.struct_list_node__aux_raw_unfolded node quarter **
    R.pts_to (N.struct_list_node__next_1 node) #quarter (L.lnext w.focus_value) **
    R.pts_to (N.struct_list_node__prev_1 node) #quarter (L.lprev w.focus_value) **
    N.struct_list_node__aux_raw_unfolded (L.lnext w.focus_value) quarter **
    R.pts_to (N.struct_list_node__next_1 (L.lnext w.focus_value))
      #quarter (L.lnext w.next_value) **
    R.pts_to (N.struct_list_node__prev_1 (L.lnext w.focus_value))
      #quarter (L.lprev w.next_value) **
    N.struct_list_node__aux_raw_unfolded (L.lprev w.focus_value) quarter **
    R.pts_to (N.struct_list_node__next_1 (L.lprev w.focus_value))
      #quarter (L.lnext w.prev_value) **
    R.pts_to (N.struct_list_node__prev_1 (L.lprev w.focus_value))
      #quarter (L.lprev w.prev_value) **
    pure (L.lprev w.next_value == node /\ L.lnext w.prev_value == node) **
    T.trade (all_fields node w) (view node w)
{
  unfold (view node w);
  N.struct_list_node__aux_raw_unfold node w.focus_value;
  N.struct_list_node__aux_raw_unfold (L.lnext w.focus_value) w.next_value;
  N.struct_list_node__aux_raw_unfold (L.lprev w.focus_value) w.prev_value;
  intro (T.trade (all_fields node w) (view node w)) #emp
  fn _ {
    unfold (all_fields node w);
    fields_open node;
    fields_open (L.lnext w.focus_value);
    fields_open (L.lprev w.focus_value);
    N.struct_list_node__aux_raw_fold node (L.lnext w.focus_value) (L.lprev w.focus_value);
    N.struct_list_node__aux_raw_fold (L.lnext w.focus_value)
      (L.lnext w.next_value) (L.lprev w.next_value);
    N.struct_list_node__aux_raw_fold (L.lprev w.focus_value)
      (L.lnext w.prev_value) (L.lprev w.prev_value);
    fold (view node w);
  };
}

ghost
fn view_close_all (node: L.lref) (#w: witness)
  requires
    N.struct_list_node__aux_raw_unfolded node quarter **
    R.pts_to (N.struct_list_node__next_1 node) #quarter (L.lnext w.focus_value) **
    R.pts_to (N.struct_list_node__prev_1 node) #quarter (L.lprev w.focus_value) **
    N.struct_list_node__aux_raw_unfolded (L.lnext w.focus_value) quarter **
    R.pts_to (N.struct_list_node__next_1 (L.lnext w.focus_value))
      #quarter (L.lnext w.next_value) **
    R.pts_to (N.struct_list_node__prev_1 (L.lnext w.focus_value))
      #quarter (L.lprev w.next_value) **
    N.struct_list_node__aux_raw_unfolded (L.lprev w.focus_value) quarter **
    R.pts_to (N.struct_list_node__next_1 (L.lprev w.focus_value))
      #quarter (L.lnext w.prev_value) **
    R.pts_to (N.struct_list_node__prev_1 (L.lprev w.focus_value))
      #quarter (L.lprev w.prev_value) **
    T.trade (all_fields node w) (view node w)
  ensures view node w
{
  fields_close node #w.focus_value;
  fields_close (L.lnext w.focus_value) #w.next_value;
  fields_close (L.lprev w.focus_value) #w.prev_value;
  fold (all_fields node w);
  T.elim_trade (all_fields node w) (view node w);
}

ghost
fn indexed_view (#a: Type0) (pl: L.ipayload a) (head node: L.lref)
                (front back: list (L.lref & a))
  requires L.is_list_ring_ix pl head 1.0R (front @ back) **
    pure (node == L.last_or head (L.cells_of front))
  ensures exists* (w: witness).
    view node w **
    T.trade (view node w)
      (L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of (front @ back))) **
    L.ipayload_of pl (front @ back)
{
  L.ring_ix_open pl head 1.0R (front @ back);
  L.cells_of_append front back;
  rewrite (L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of (front @ back)))
    as (L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of front @ L.cells_of back));
  ring_view L.emp_pl head node (L.cells_of front) (L.cells_of back);
  with w. assert (view node w);
  rewrite (T.trade (view node w)
    (L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of front @ L.cells_of back)))
    as (T.trade (view node w)
      (L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of (front @ back))));
}

ghost
fn restore_indexed (#a: Type0) (pl: L.ipayload a) (head node: L.lref)
                   (es: list (L.lref & a)) (#w: witness)
  requires view node w **
    T.trade (view node w) (L.is_list_ring_with L.emp_pl head 1.0R (L.cells_of es)) **
    L.ipayload_of pl es
  ensures L.is_list_ring_ix pl head 1.0R es
{
  restore_ring L.emp_pl head node (L.cells_of es);
  L.ring_ix_close pl head 1.0R es;
}
