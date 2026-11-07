module IntrusiveListValidate

(* Neighbor reads borrow fractional link ownership and restore the same witness.
   Only link storage is shared; the indexed payload bundle is framed once. *)

open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module R = IntrusiveListNodeRef
module N = Struct_list_node
module X = IntrusiveListIndexed
module T = Pulse.Lib.Trade

unfold let quarter : perm = 0.25R

unfold let segment (#a: Type0) (prev cur endl: X.lref) (p: perm) (es: X.entries a) =
  X.is_list_seg_ix X.no_payload prev cur endl p es

unfold let ring (#a: Type0) (head: X.lref) (p: perm) (es: X.entries a) =
  X.is_list_ring_ix X.no_payload head p es

let held (r: X.lref) (p: perm) (v: N.struct_list_node) = R.pts_to r #p v

(* Only the empty-payload specialization is shared; descriptions stay indexed. *)
ghost
fn rec seg_share (#a: Type0) (prev cur endl: X.lref) (p: perm) (es: X.entries a)
  requires segment prev cur endl p es
  ensures segment prev cur endl (p /. 2.0R) es **
    segment prev cur endl (p /. 2.0R) es
  decreases es
{
  match es {
    Nil -> {
      X.seg_nil_elim X.no_payload prev cur endl p;
      X.seg_nil_intro (X.no_payload #a) prev cur endl (p /. 2.0R);
      X.seg_nil_intro (X.no_payload #a) prev cur endl (p /. 2.0R);
    }
    Cons e rest -> {
      X.seg_cons_elim X.no_payload prev cur endl p e rest;
      with v. assert (R.pts_to cur #p v);
      R.share cur;
      seg_share cur (X.lnext v) endl p rest;
      X.seg_cons_intro X.no_payload prev cur endl (p /. 2.0R) e rest;
      X.seg_cons_intro X.no_payload prev cur endl (p /. 2.0R) e rest;
    }
  }
}

ghost
fn rec seg_gather (#a: Type0) (prev cur endl: X.lref) (p: perm { p <=. 0.5R })
                  (es: X.entries a)
  requires segment prev cur endl p es ** segment prev cur endl p es
  ensures segment prev cur endl (p +. p) es
  decreases es
{
  match es {
    Nil -> {
      X.seg_nil_elim X.no_payload prev cur endl p;
      X.seg_nil_elim X.no_payload prev cur endl p;
      X.seg_nil_intro (X.no_payload #a) prev cur endl (p +. p);
    }
    Cons e rest -> {
      X.seg_cons_elim X.no_payload prev cur endl p e rest;
      with v1. assert (R.pts_to cur #p v1);
      fold (held cur p v1);
      X.seg_cons_elim X.no_payload prev cur endl p e rest;
      with v2. assert (R.pts_to cur #p v2);
      unfold (held cur p v1);
      R.gather cur #(hide v1) #(hide v2) #p #p;
      rewrite (segment cur (X.lnext v2) endl p rest)
        as (segment cur (X.lnext v1) endl p rest);
      seg_gather cur (X.lnext v1) endl p rest;
      X.seg_cons_intro X.no_payload prev cur endl (p +. p) e rest;
    }
  }
}

ghost
fn ring_share (#a: Type0) (head: X.lref) (p: perm) (es: X.entries a)
  requires ring head p es
  ensures ring head (p /. 2.0R) es ** ring head (p /. 2.0R) es
{
  X.ring_open X.no_payload head;
  with hv. assert (R.pts_to head #p hv);
  R.share head;
  seg_share head (X.lnext hv) head p es;
  X.ring_close X.no_payload head;
  X.ring_close X.no_payload head;
}

ghost
fn ring_gather (#a: Type0) (head: X.lref) (p: perm { p <=. 0.5R }) (es: X.entries a)
  requires ring head p es ** ring head p es
  ensures ring head (p +. p) es
{
  X.ring_open X.no_payload head;
  with hv1. assert (R.pts_to head #p hv1);
  fold (held head p hv1);
  X.ring_open X.no_payload head;
  with hv2. assert (R.pts_to head #p hv2);
  unfold (held head p hv1);
  R.gather head #(hide hv1) #(hide hv2) #p #p;
  rewrite (segment head (X.lnext hv2) head p es)
    as (segment head (X.lnext hv1) head p es);
  seg_gather head (X.lnext hv1) head p es;
  X.ring_close X.no_payload head;
}

ghost
fn ring_quarters (#a: Type0) (head: X.lref) (es: X.entries a)
  requires ring head 1.0R es
  ensures ring head quarter es ** ring head quarter es **
    ring head quarter es ** ring head quarter es
{
  ring_share head 1.0R es;
  rewrite (ring head (1.0R /. 2.0R) es) as (ring head 0.5R es);
  rewrite (ring head (1.0R /. 2.0R) es) as (ring head 0.5R es);
  ring_share head 0.5R es;
  ring_share head 0.5R es;
  rewrite (ring head (0.5R /. 2.0R) es) as (ring head quarter es);
  rewrite (ring head (0.5R /. 2.0R) es) as (ring head quarter es);
  rewrite (ring head (0.5R /. 2.0R) es) as (ring head quarter es);
  rewrite (ring head (0.5R /. 2.0R) es) as (ring head quarter es);
}

ghost
fn ring_unquarters (#a: Type0) (head: X.lref) (es: X.entries a)
  requires ring head quarter es ** ring head quarter es **
    ring head quarter es ** ring head quarter es
  ensures ring head 1.0R es
{
  ring_gather head quarter es;
  ring_gather head quarter es;
  rewrite (ring head (quarter +. quarter) es) as (ring head 0.5R es);
  rewrite (ring head (quarter +. quarter) es) as (ring head 0.5R es);
  ring_gather head 0.5R es;
  rewrite (ring head (0.5R +. 0.5R) es) as (ring head 1.0R es);
}

ghost
fn rec seg_borrow (#a: Type0) (prev cur endl: X.lref) (p: perm)
                  (front: X.entries a) (e: X.entry a) (back: X.entries a)
  requires segment prev cur endl p (front @ (e :: back))
  ensures
    R.pts_to (fst e) #p (X.mklink (X.first_or endl back) (X.last_or prev front)) **
    T.trade
      (R.pts_to (fst e) #p (X.mklink (X.first_or endl back) (X.last_or prev front)))
      (segment prev cur endl p (front @ (e :: back)))
  decreases front
{
  match front {
    Nil -> {
      X.seg_cons_elim X.no_payload prev cur endl p e back;
      with v. assert (R.pts_to cur #p v);
      X.seg_first X.no_payload cur (X.lnext v) endl;
      rewrite (R.pts_to cur #p v)
        as (R.pts_to (fst e) #p (X.mklink (X.first_or endl back) prev));
      intro (T.trade
        (R.pts_to (fst e) #p (X.mklink (X.first_or endl back) prev))
        (segment prev cur endl p (front @ (e :: back))))
        #(segment cur (X.lnext v) endl p back)
      fn _ {
        rewrite (R.pts_to (fst e) #p (X.mklink (X.first_or endl back) prev))
          as (R.pts_to cur #p v);
        X.seg_cons_intro X.no_payload prev cur endl p e back;
      };
    }
    Cons hd rest -> {
      X.seg_cons_elim X.no_payload prev cur endl p hd (rest @ (e :: back));
      with v. assert (R.pts_to cur #p v);
      seg_borrow cur (X.lnext v) endl p rest e back;
      let nv = X.mklink (X.first_or endl back) (X.last_or prev front);
      rewrite (R.pts_to (fst e) #p (X.mklink (X.first_or endl back) (X.last_or cur rest)))
        as (R.pts_to (fst e) #p nv);
      intro (T.trade (R.pts_to (fst e) #p nv)
        (segment prev cur endl p (front @ (e :: back))))
        #(R.pts_to cur #p v **
          T.trade
            (R.pts_to (fst e) #p (X.mklink (X.first_or endl back) (X.last_or cur rest)))
            (segment cur (X.lnext v) endl p (rest @ (e :: back))))
      fn _ {
        rewrite (R.pts_to (fst e) #p nv)
          as (R.pts_to (fst e) #p (X.mklink (X.first_or endl back) (X.last_or cur rest)));
        T.elim_trade
          (R.pts_to (fst e) #p (X.mklink (X.first_or endl back) (X.last_or cur rest)))
          (segment cur (X.lnext v) endl p (rest @ (e :: back)));
        X.seg_cons_intro X.no_payload prev cur endl p hd (rest @ (e :: back));
      };
    }
  }
}

ghost
fn borrow_head (#a: Type0) (head: X.lref) (p: perm) (es: X.entries a)
  requires ring head p es
  ensures
    R.pts_to head #p (X.mklink (X.first_or head es) (X.last_or head es)) **
    T.trade
      (R.pts_to head #p (X.mklink (X.first_or head es) (X.last_or head es)))
      (ring head p es)
{
  X.ring_open X.no_payload head;
  with hv. assert (R.pts_to head #p hv);
  let v = X.mklink (X.first_or head es) (X.last_or head es);
  rewrite (R.pts_to head #p hv) as (R.pts_to head #p v);
  intro (T.trade (R.pts_to head #p v) (ring head p es))
    #(segment head (X.lnext hv) head p es)
  fn _ {
    rewrite (R.pts_to head #p v) as (R.pts_to head #p hv);
    X.ring_close X.no_payload head;
  };
}

ghost
fn borrow_member (#a: Type0) (head: X.lref) (p: perm)
                 (front: X.entries a) (e: X.entry a) (back: X.entries a)
  requires ring head p (front @ (e :: back))
  ensures
    R.pts_to (fst e) #p (X.mklink (X.first_or head back) (X.last_or head front)) **
    T.trade
      (R.pts_to (fst e) #p (X.mklink (X.first_or head back) (X.last_or head front)))
      (ring head p (front @ (e :: back)))
{
  X.ring_open X.no_payload head;
  with hv. assert (R.pts_to head #p hv);
  seg_borrow head (X.lnext hv) head p front e back;
  let v = X.mklink (X.first_or head back) (X.last_or head front);
  intro (T.trade (R.pts_to (fst e) #p v) (ring head p (front @ (e :: back))))
    #(R.pts_to head #p hv **
      T.trade (R.pts_to (fst e) #p v)
        (segment head (X.lnext hv) head p (front @ (e :: back))))
  fn _ {
    T.elim_trade (R.pts_to (fst e) #p v)
      (segment head (X.lnext hv) head p (front @ (e :: back)));
    X.ring_close X.no_payload head;
  };
}

let rec init_last (#a: Type0) (es: X.entries a { Cons? es })
  : Lemma (init es @ [last es] == es) (decreases es)
  = match es with | [_] -> () | _ :: rest -> init_last rest

let rec last_is_last (#a: Type0) (head: X.lref) (es: X.entries a { Cons? es })
  : Lemma (X.last_or head es == fst (last es)) (decreases es)
  = match es with | [_] -> () | e :: rest -> last_is_last (fst e) rest

ghost
fn borrow_successor (#a: Type0) (head: X.lref) (p: perm)
                    (front: X.entries a) (e: X.entry a) (back: X.entries a)
  requires ring head p (front @ (e :: back))
  ensures exists* (v: N.struct_list_node).
    R.pts_to (X.first_or head back) #p v ** pure (X.lprev v == fst e) **
    T.trade (R.pts_to (X.first_or head back) #p v) (ring head p (front @ (e :: back)))
{
  match back {
    Nil -> {
      X.last_or_snoc head front e;
      borrow_head head p (front @ [e]);
    }
    Cons hd rest -> {
      FStar.List.Tot.Properties.append_assoc front [e] (hd :: rest);
      X.last_or_snoc head front e;
      rewrite (ring head p (front @ (e :: back)))
        as (ring head p ((front @ [e]) @ (hd :: rest)));
      borrow_member head p (front @ [e]) hd rest;
      let v = X.mklink (X.first_or head rest) (X.last_or head (front @ [e]));
      rewrite (T.trade (R.pts_to (fst hd) #p v)
        (ring head p ((front @ [e]) @ (hd :: rest))))
        as (T.trade (R.pts_to (X.first_or head back) #p v)
          (ring head p (front @ (e :: back))));
    }
  }
}

ghost
fn borrow_predecessor (#a: Type0) (head: X.lref) (p: perm)
                      (front: X.entries a) (e: X.entry a) (back: X.entries a)
  requires ring head p (front @ (e :: back))
  ensures exists* (v: N.struct_list_node).
    R.pts_to (X.last_or head front) #p v ** pure (X.lnext v == fst e) **
    T.trade (R.pts_to (X.last_or head front) #p v) (ring head p (front @ (e :: back)))
{
  match front {
    Nil -> { borrow_head head p (e :: back); }
    Cons hd rest -> {
      init_last front;
      last_is_last head front;
      FStar.List.Tot.Properties.append_assoc (init front) [last front] (e :: back);
      rewrite (ring head p (front @ (e :: back)))
        as (ring head p (init front @ (last front :: e :: back)));
      borrow_member head p (init front) (last front) (e :: back);
      let v = X.mklink (fst e) (X.last_or head (init front));
      rewrite (R.pts_to (fst (last front)) #p v)
        as (R.pts_to (X.last_or head front) #p v);
      rewrite (T.trade (R.pts_to (fst (last front)) #p v)
        (ring head p (init front @ (last front :: e :: back))))
        as (T.trade (R.pts_to (X.last_or head front) #p v)
          (ring head p (front @ (e :: back))));
    }
  }
}

ghost
fn borrow_first (#a: Type0) (head: X.lref) (p: perm) (es: X.entries a)
  requires ring head p es
  ensures exists* (v: N.struct_list_node).
    R.pts_to (X.first_or head es) #p v ** pure (X.lprev v == head) **
    T.trade (R.pts_to (X.first_or head es) #p v) (ring head p es)
{
  match es {
    Nil -> { borrow_head head p es; }
    Cons e rest -> { borrow_member head p [] e rest; }
  }
}

ghost
fn borrow_last (#a: Type0) (head: X.lref) (p: perm) (es: X.entries a)
  requires ring head p es
  ensures exists* (v: N.struct_list_node).
    R.pts_to (X.last_or head es) #p v ** pure (X.lnext v == head) **
    T.trade (R.pts_to (X.last_or head es) #p v) (ring head p es)
{
  match es {
    Nil -> { borrow_head head p es; }
    Cons e rest -> {
      init_last es;
      last_is_last head es;
      rewrite (ring head p es) as (ring head p (init es @ [last es]));
      borrow_member head p (init es) (last es) [];
      let v = X.mklink head (X.last_or head (init es));
      rewrite (R.pts_to (fst (last es)) #p v) as (R.pts_to (X.last_or head es) #p v);
      rewrite (T.trade (R.pts_to (fst (last es)) #p v) (ring head p (init es @ [last es])))
        as (T.trade (R.pts_to (X.last_or head es) #p v) (ring head p es));
    }
  }
}

noeq type witness = {
  focus_value: N.struct_list_node;
  next_value: N.struct_list_node;
  prev_value: N.struct_list_node;
}

(* Even three aliases use only three quarters. The witness fixes returned values. *)
let view (node: X.lref) (w: witness) : slprop =
  R.pts_to node #quarter w.focus_value **
  R.pts_to (X.lnext w.focus_value) #quarter w.next_value **
  R.pts_to (X.lprev w.focus_value) #quarter w.prev_value **
  pure (X.lprev w.next_value == node /\ X.lnext w.prev_value == node)

ghost
fn view_from_borrows (#a: Type0) (pl: X.ipayload a) (head node: X.lref)
                    (es: X.entries a) (v nv pv: N.struct_list_node)
  requires R.pts_to node #quarter v **
    R.pts_to (X.lnext v) #quarter nv ** R.pts_to (X.lprev v) #quarter pv **
    pure (X.lprev nv == node /\ X.lnext pv == node) **
    T.trade (R.pts_to node #quarter v) (ring head quarter es) **
    T.trade (R.pts_to (X.lnext v) #quarter nv) (ring head quarter es) **
    T.trade (R.pts_to (X.lprev v) #quarter pv) (ring head quarter es) **
    ring head quarter es ** X.ipayload_of pl es
  ensures exists* (w: witness).
    view node w ** T.trade (view node w) (X.is_list_ring_ix pl head 1.0R es)
{
  let w = { focus_value = v; next_value = nv; prev_value = pv };
  rewrite (R.pts_to (X.lnext v) #quarter nv)
    as (R.pts_to (X.lnext w.focus_value) #quarter w.next_value);
  rewrite (R.pts_to (X.lprev v) #quarter pv)
    as (R.pts_to (X.lprev w.focus_value) #quarter w.prev_value);
  fold (view node w);
  intro (T.trade (view node w) (X.is_list_ring_ix pl head 1.0R es))
    #(T.trade (R.pts_to node #quarter v) (ring head quarter es) **
      T.trade (R.pts_to (X.lnext v) #quarter nv) (ring head quarter es) **
      T.trade (R.pts_to (X.lprev v) #quarter pv) (ring head quarter es) **
      ring head quarter es ** X.ipayload_of pl es)
  fn _ {
    unfold (view node w);
    rewrite (R.pts_to (X.lnext w.focus_value) #quarter w.next_value)
      as (R.pts_to (X.lnext v) #quarter nv);
    rewrite (R.pts_to (X.lprev w.focus_value) #quarter w.prev_value)
      as (R.pts_to (X.lprev v) #quarter pv);
    T.elim_trade (R.pts_to node #quarter v) (ring head quarter es);
    T.elim_trade (R.pts_to (X.lnext v) #quarter nv) (ring head quarter es);
    T.elim_trade (R.pts_to (X.lprev v) #quarter pv) (ring head quarter es);
    ring_unquarters head es;
    X.ring_pl_in pl head 1.0R es;
  };
}

ghost
fn member_view (#a: Type0) (pl: X.ipayload a) (head node: X.lref)
               (front: X.entries a) (description: a) (back: X.entries a)
  requires X.is_list_ring_ix pl head 1.0R (front @ ((node, description) :: back))
  ensures exists* (w: witness).
    view node w ** T.trade (view node w)
      (X.is_list_ring_ix pl head 1.0R (front @ ((node, description) :: back)))
{
  X.ring_pl_out pl head 1.0R (front @ ((node, description) :: back));
  ring_quarters head (front @ ((node, description) :: back));
  borrow_member head quarter front (node, description) back;
  let v = X.mklink (X.first_or head back) (X.last_or head front);
  fold (held node quarter v);
  borrow_successor head quarter front (node, description) back;
  with nv. assert (R.pts_to (X.first_or head back) #quarter nv);
  fold (held (X.first_or head back) quarter nv);
  borrow_predecessor head quarter front (node, description) back;
  with pv. assert (R.pts_to (X.last_or head front) #quarter pv);
  unfold (held node quarter v);
  unfold (held (X.first_or head back) quarter nv);
  rewrite (R.pts_to (X.first_or head back) #quarter nv) as (R.pts_to (X.lnext v) #quarter nv);
  rewrite (R.pts_to (X.last_or head front) #quarter pv) as (R.pts_to (X.lprev v) #quarter pv);
  rewrite (T.trade (R.pts_to (X.first_or head back) #quarter nv)
    (ring head quarter (front @ ((node, description) :: back))))
    as (T.trade (R.pts_to (X.lnext v) #quarter nv)
      (ring head quarter (front @ ((node, description) :: back))));
  rewrite (T.trade (R.pts_to (X.last_or head front) #quarter pv)
    (ring head quarter (front @ ((node, description) :: back))))
    as (T.trade (R.pts_to (X.lprev v) #quarter pv)
      (ring head quarter (front @ ((node, description) :: back))));
  view_from_borrows pl head node (front @ ((node, description) :: back)) v nv pv;
}

ghost
fn sentinel_view (#a: Type0) (pl: X.ipayload a) (head: X.lref) (es: X.entries a)
  requires X.is_list_ring_ix pl head 1.0R es
  ensures exists* (w: witness).
    view head w ** T.trade (view head w) (X.is_list_ring_ix pl head 1.0R es)
{
  X.ring_pl_out pl head 1.0R es;
  ring_quarters head es;
  borrow_head head quarter es;
  let v = X.mklink (X.first_or head es) (X.last_or head es);
  fold (held head quarter v);
  borrow_first head quarter es;
  with nv. assert (R.pts_to (X.first_or head es) #quarter nv);
  fold (held (X.first_or head es) quarter nv);
  borrow_last head quarter es;
  with pv. assert (R.pts_to (X.last_or head es) #quarter pv);
  unfold (held head quarter v);
  unfold (held (X.first_or head es) quarter nv);
  rewrite (R.pts_to (X.first_or head es) #quarter nv) as (R.pts_to (X.lnext v) #quarter nv);
  rewrite (R.pts_to (X.last_or head es) #quarter pv) as (R.pts_to (X.lprev v) #quarter pv);
  rewrite (T.trade (R.pts_to (X.first_or head es) #quarter nv) (ring head quarter es))
    as (T.trade (R.pts_to (X.lnext v) #quarter nv) (ring head quarter es));
  rewrite (T.trade (R.pts_to (X.last_or head es) #quarter pv) (ring head quarter es))
    as (T.trade (R.pts_to (X.lprev v) #quarter pv) (ring head quarter es));
  view_from_borrows pl head head es v nv pv;
}

ghost
fn rec member_at (#a: Type0) (pl: X.ipayload a) (head node: X.lref)
                 (front back: X.entries a)
  requires X.is_list_ring_ix pl head 1.0R (front @ back) **
    pure (memP node (X.cells_of back))
  ensures exists* (w: witness).
    view node w ** T.trade (view node w) (X.is_list_ring_ix pl head 1.0R (front @ back))
  decreases back
{
  match back {
    Nil -> { unreachable (); }
    Cons e rest -> {
      if (R.ref_eq node (fst e)) {
        rewrite (X.is_list_ring_ix pl head 1.0R (front @ back))
          as (X.is_list_ring_ix pl head 1.0R (front @ ((node, snd e) :: rest)));
        member_view pl head node front (snd e) rest;
        with w. assert (view node w);
        rewrite (T.trade (view node w)
          (X.is_list_ring_ix pl head 1.0R (front @ ((node, snd e) :: rest))))
          as (T.trade (view node w) (X.is_list_ring_ix pl head 1.0R (front @ back)));
      } else {
        FStar.List.Tot.Properties.append_assoc front [e] rest;
        rewrite (X.is_list_ring_ix pl head 1.0R (front @ back))
          as (X.is_list_ring_ix pl head 1.0R ((front @ [e]) @ rest));
        member_at pl head node (front @ [e]) rest;
        with w. assert (view node w);
        rewrite (T.trade (view node w) (X.is_list_ring_ix pl head 1.0R ((front @ [e]) @ rest)))
          as (T.trade (view node w) (X.is_list_ring_ix pl head 1.0R (front @ back)));
      }
    }
  }
}

ghost
fn begin_validation (#a: Type0) (pl: X.ipayload a) (head node: X.lref) (es: X.entries a)
  requires X.is_list_ring_ix pl head 1.0R es **
    pure (node == head \/ memP node (X.cells_of es))
  ensures exists* (w: witness).
    view node w ** T.trade (view node w) (X.is_list_ring_ix pl head 1.0R es)
{
  if (R.ref_eq node head) {
    rewrite (X.is_list_ring_ix pl head 1.0R es) as (X.is_list_ring_ix pl node 1.0R es);
    sentinel_view pl node es;
    with w. assert (view node w);
    rewrite (T.trade (view node w) (X.is_list_ring_ix pl node 1.0R es))
      as (T.trade (view node w) (X.is_list_ring_ix pl head 1.0R es));
  } else {
    rewrite (X.is_list_ring_ix pl head 1.0R es) as (X.is_list_ring_ix pl head 1.0R ([] @ es));
    member_at pl head node [] es;
  }
}

ghost
fn end_validation (#a: Type0) (pl: X.ipayload a) (head node: X.lref)
                  (es: X.entries a) (#w: witness)
  requires view node w ** T.trade (view node w) (X.is_list_ring_ix pl head 1.0R es)
  ensures X.is_list_ring_ix pl head 1.0R es
{
  T.elim_trade (view node w) (X.is_list_ring_ix pl head 1.0R es);
}

ghost
fn ring_view (#a: Type0) (pl: X.ipayload a) (head node: X.lref)
             (front back: X.entries a)
  requires X.is_list_ring_ix pl head 1.0R (front @ back) **
    pure (node == X.last_or head front)
  ensures exists* (w: witness).
    view node w **
    T.trade (view node w) (X.is_list_ring_ix pl head 1.0R (front @ back))
{
  match front {
    Nil -> {
      rewrite (X.is_list_ring_ix pl head 1.0R (front @ back))
        as (X.is_list_ring_ix pl node 1.0R back);
      sentinel_view pl node back;
      with w. assert (view node w);
      rewrite (T.trade (view node w) (X.is_list_ring_ix pl node 1.0R back))
        as (T.trade (view node w) (X.is_list_ring_ix pl head 1.0R (front @ back)));
    }
    Cons e rest -> {
      init_last front;
      last_is_last head front;
      FStar.List.Tot.Properties.append_assoc (init front) [last front] back;
      rewrite (X.is_list_ring_ix pl head 1.0R (front @ back))
        as (X.is_list_ring_ix pl head 1.0R
          (init front @ ((node, snd (last front)) :: back)));
      member_view pl head node (init front) (snd (last front)) back;
      with w. assert (view node w);
      rewrite (T.trade (view node w) (X.is_list_ring_ix pl head 1.0R
        (init front @ ((node, snd (last front)) :: back))))
        as (T.trade (view node w) (X.is_list_ring_ix pl head 1.0R (front @ back)));
    }
  }
}

ghost
fn restore_ring (#a: Type0) (pl: X.ipayload a) (head node: X.lref)
                (es: X.entries a) (#w: witness)
  requires view node w ** T.trade (view node w) (X.is_list_ring_ix pl head 1.0R es)
  ensures X.is_list_ring_ix pl head 1.0R es
{
  end_validation pl head node es;
}

(* The three nodes the assertions read, handed over whole. Under the current
   model this pair opened each node into one reference per field, because that
   is what a field read needs there; Palow reads a field in place, so the
   points-to itself is what crosses. *)
let all_fields (node: X.lref) (w: witness) =
  R.pts_to node #quarter w.focus_value **
  R.pts_to (X.lnext w.focus_value) #quarter w.next_value **
  R.pts_to (X.lprev w.focus_value) #quarter w.prev_value

ghost
fn view_open_all (node: X.lref) (#w: witness)
  requires view node w
  ensures
    R.pts_to node #quarter w.focus_value **
    R.pts_to (X.lnext w.focus_value) #quarter w.next_value **
    R.pts_to (X.lprev w.focus_value) #quarter w.prev_value **
    pure (X.lprev w.next_value == node /\ X.lnext w.prev_value == node) **
    T.trade (all_fields node w) (view node w)
{
  unfold (view node w);
  intro (T.trade (all_fields node w) (view node w)) #emp
  fn _ {
    unfold (all_fields node w);
    fold (view node w);
  };
}

ghost
fn view_close_all (node: X.lref) (#w: witness)
  requires
    R.pts_to node #quarter w.focus_value **
    R.pts_to (X.lnext w.focus_value) #quarter w.next_value **
    R.pts_to (X.lprev w.focus_value) #quarter w.prev_value **
    T.trade (all_fields node w) (view node w)
  ensures view node w
{
  fold (all_fields node w);
  T.elim_trade (all_fields node w) (view node w);
}
