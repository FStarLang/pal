module IntrusiveList
open Pulse
open Pulse.Lib.C
open FStar.List.Tot
#lang-pulse

module R = Pulse.Lib.Reference
module L = Struct_list_node
module T = Pulse.Lib.Trade

unfold let lref = ref L.struct_list_node
unfold let lnext (v: L.struct_list_node) : lref = v.L.struct_list_node__next
unfold let lprev (v: L.struct_list_node) : lref = v.L.struct_list_node__prev

unfold let mklink (n p: lref) : L.struct_list_node = {
  L.struct_list_node__next = n;
  L.struct_list_node__prev = p;
}

(* Payload ownership is independent of the mutable links. *)
let payload = lref -> slprop

let rec last_or (d: lref) (cs: list lref)
  : Tot lref (decreases cs)
  = match cs with
    | [] -> d
    | [x] -> x
    | _ :: tl -> last_or d tl

(* The endpoint is excluded; each owned cell points back to its predecessor. *)
let rec is_list_seg_with
    (pl: payload)
    (prev: lref)
    (cur: lref)
    (endl: lref)
    (p: perm)
    (cells: list lref)
  : Tot slprop (decreases cells)
  = match cells with
    | [] -> pure (cur == endl)
    | hd :: tl ->
      pure (cur == hd) **
      pure (cur =!= endl) **
      (exists* (v: L.struct_list_node).
        R.pts_to cur #p v **
        pl cur **
        pure (lprev v == prev) **
        is_list_seg_with pl cur (lnext v) endl p tl)

(* The sentinel closes the segment and carries no member payload. *)
let is_list_ring_with
    (pl: payload)
    ([@@@mkey] head: lref)
    (p: perm)
    (cells: list lref)
  : slprop
  = exists* (hv: L.struct_list_node).
      R.pts_to head #p hv **
      is_list_seg_with pl head (lnext hv) head p cells **
      pure (lprev hv == last_or head cells)

unfold let no_payload : payload = fun _ -> emp

unfold let is_list_seg (prev cur endl: lref) (p: perm) (cells: list lref) : slprop =
  is_list_seg_with no_payload prev cur endl p cells

unfold let is_list_ring (head: lref) (p: perm) (cells: list lref) : slprop =
  is_list_ring_with no_payload head p cells

ghost
fn ring_unfold (pl: payload) (head: lref) (#p: perm) (#cells: list lref)
  requires is_list_ring_with pl head p cells
  returns _: unit
  ensures
    exists* (hv: L.struct_list_node).
      R.pts_to head #p hv **
      is_list_seg_with pl head (lnext hv) head p cells **
      pure (lprev hv == last_or head cells)
{
  unfold (is_list_ring_with pl head p cells);
}

ghost
fn ring_fold (pl: payload) (head: lref) (#p: perm) (#cells: list lref)
             (#hv: L.struct_list_node)
  requires
    R.pts_to head #p hv **
    is_list_seg_with pl head (lnext hv) head p cells **
    pure (lprev hv == last_or head cells)
  returns _: unit
  ensures is_list_ring_with pl head p cells
{
  fold (is_list_ring_with pl head p cells);
}

ghost
fn seg_nil_intro (pl: payload) (prev cur endl: lref) (p: perm)
  requires pure (cur == endl)
  returns _: unit
  ensures is_list_seg_with pl prev cur endl p []
{
  fold (is_list_seg_with pl prev cur endl p (Nil #lref));
}

ghost
fn seg_nil_elim (pl: payload) (prev cur endl: lref) (p: perm)
  requires is_list_seg_with pl prev cur endl p []
  returns _: unit
  ensures pure (cur == endl)
{
  unfold (is_list_seg_with pl prev cur endl p (Nil #lref));
}

ghost
fn seg_cons_intro (pl: payload) (prev cur endl: lref) (p: perm) (hd: lref) (tl: list lref)
                  (#v: L.struct_list_node)
  requires
    R.pts_to cur #p v **
    pl cur **
    pure (cur == hd) **
    pure (lprev v == prev) **
    pure (cur =!= endl) **
    is_list_seg_with pl cur (lnext v) endl p tl
  returns _: unit
  ensures is_list_seg_with pl prev cur endl p (hd :: tl)
{
  fold (is_list_seg_with pl prev cur endl p (hd :: tl));
}

ghost
fn seg_cons_elim (pl: payload) (prev cur endl: lref) (p: perm) (hd: lref) (tl: list lref)
  requires is_list_seg_with pl prev cur endl p (hd :: tl)
  returns _: unit
  ensures
    exists* (v: L.struct_list_node).
      R.pts_to cur #p v **
      pl cur **
      pure (cur == hd) **
      pure (cur =!= endl) **
      pure (lprev v == prev) **
      is_list_seg_with pl cur (lnext v) endl p tl
{
  unfold (is_list_seg_with pl prev cur endl p (hd :: tl));
}

ghost
fn ring_intro_empty (pl: payload) (head: lref) (#p: perm) (#hv: L.struct_list_node)
  requires
    R.pts_to head #p hv **
    pure (lnext hv == head) **
    pure (lprev hv == head)
  returns _: unit
  ensures is_list_ring_with pl head p []
{
  seg_nil_intro pl head (lnext hv) head p;
  fold (is_list_ring_with pl head p []);
}

ghost
fn ring_elim_empty (pl: payload) (head: lref) (#p: perm)
  requires is_list_ring_with pl head p []
  returns _: unit
  ensures
    exists* (hv: L.struct_list_node).
      R.pts_to head #p hv **
      pure (lnext hv == head) **
      pure (lprev hv == head)
{
  unfold (is_list_ring_with pl head p []);
  with hv. assert (R.pts_to head #p hv);
  seg_nil_elim pl head (lnext hv) head p;
}

ghost
fn ring_empty_repl (pl1 pl2: payload) (head: lref) (#p: perm)
  requires is_list_ring_with pl1 head p []
  returns _: unit
  ensures is_list_ring_with pl2 head p []
{
  ring_elim_empty pl1 head;
  ring_intro_empty pl2 head;
}

ghost
fn refs_distinct (#a: Type0) (r1 r2: R.ref a) (#v1 #v2: a)
  requires R.pts_to r1 #1.0R v1 ** R.pts_to r2 #1.0R v2
  returns _: unit
  ensures R.pts_to r1 #1.0R v1 ** R.pts_to r2 #1.0R v2 ** pure (r1 =!= r2)
{
  let b = FStar.IndefiniteDescription.strong_excluded_middle (r1 == r2);
  if b {
    rewrite (R.pts_to r2 #1.0R v2) as (R.pts_to r1 #1.0R v2);
    R.gather r1;
    R.pts_to_perm_bound r1;
    unreachable ()
  } else {
    ()
  }
}

ghost
fn ring_nonempty_head_distinct (pl: payload) (head: lref) (#p: perm)
                               (hd: lref) (tl: list lref)
  requires is_list_ring_with pl head p (hd :: tl)
  returns _: unit
  ensures is_list_ring_with pl head p (hd :: tl) ** pure (hd =!= head)
{
  unfold (is_list_ring_with pl head p (hd :: tl));
  with hv. assert (R.pts_to head #p hv);
  unfold (is_list_seg_with pl head (lnext hv) head p (hd :: tl));
  fold (is_list_seg_with pl head (lnext hv) head p (hd :: tl));
  fold (is_list_ring_with pl head p (hd :: tl));
}

let rec payload_of (pl: payload) (cs: list lref) : Tot slprop (decreases cs) =
  match cs with
  | [] -> emp
  | c :: tl -> pl c ** payload_of pl tl

ghost
fn rec payload_of_split (pl: payload) (a b: list lref)
  requires payload_of pl (a @ b)
  returns _: unit
  ensures payload_of pl a ** payload_of pl b
  decreases a
{
  match a {
    Nil -> {
      rewrite (payload_of pl (a @ b)) as (payload_of pl b);
      fold (payload_of pl (Nil #lref));
      rewrite (payload_of pl (Nil #lref)) as (payload_of pl a);
    }
    Cons a0 at -> {
      rewrite (payload_of pl (a @ b)) as (payload_of pl (a0 :: (at @ b)));
      unfold (payload_of pl (a0 :: (at @ b)));
      payload_of_split pl at b;
      fold (payload_of pl (a0 :: at));
      rewrite (payload_of pl (a0 :: at)) as (payload_of pl a);
    }
  }
}

ghost
fn rec payload_of_join (pl: payload) (a b: list lref)
  requires payload_of pl a ** payload_of pl b
  returns _: unit
  ensures payload_of pl (a @ b)
  decreases a
{
  match a {
    Nil -> {
      rewrite (payload_of pl a) as (payload_of pl (Nil #lref));
      unfold (payload_of pl (Nil #lref));
      rewrite (payload_of pl b) as (payload_of pl (a @ b));
    }
    Cons a0 at -> {
      rewrite (payload_of pl a) as (payload_of pl (a0 :: at));
      unfold (payload_of pl (a0 :: at));
      payload_of_join pl at b;
      fold (payload_of pl (a0 :: (at @ b)));
      rewrite (payload_of pl (a0 :: (at @ b))) as (payload_of pl (a @ b));
    }
  }
}

ghost
fn payload_of_single_in (pl: payload) (c: lref)
  requires pl c
  returns _: unit
  ensures payload_of pl [c]
{
  fold (payload_of pl (Nil #lref));
  fold (payload_of pl [c]);
}

ghost
fn payload_of_single_out (pl: payload) (c: lref)
  requires payload_of pl [c]
  returns _: unit
  ensures pl c
{
  unfold (payload_of pl [c]);
  unfold (payload_of pl (Nil #lref));
}

ghost
fn payload_of_insert (pl: payload) (front back: list lref) (nw: lref)
  requires payload_of pl (front @ back) ** pl nw
  returns _: unit
  ensures payload_of pl (front @ (nw :: back))
{
  payload_of_split pl front back;
  fold (payload_of pl (nw :: back));
  payload_of_join pl front (nw :: back);
}

ghost
fn payload_of_remove (pl: payload) (front back: list lref) (ent: lref)
  requires payload_of pl (front @ (ent :: back))
  returns _: unit
  ensures payload_of pl (front @ back) ** pl ent
{
  payload_of_split pl front (ent :: back);
  unfold (payload_of pl (ent :: back));
  payload_of_join pl front back;
}

ghost
fn rec seg_pl_out (pl: payload) (prev cur endl: lref) (p: perm) (cs: list lref)
  requires is_list_seg_with pl prev cur endl p cs
  returns _: unit
  ensures is_list_seg_with no_payload prev cur endl p cs ** payload_of pl cs
  decreases cs
{
  match cs {
    Nil -> {
      rewrite (is_list_seg_with pl prev cur endl p cs)
           as (is_list_seg_with pl prev cur endl p (Nil #lref));
      seg_nil_elim pl prev cur endl p;
      seg_nil_intro no_payload prev cur endl p;
      fold (payload_of pl (Nil #lref));
      rewrite (is_list_seg_with no_payload prev cur endl p (Nil #lref)
               ** payload_of pl (Nil #lref))
           as (is_list_seg_with no_payload prev cur endl p cs ** payload_of pl cs);
    }
    Cons c0 ct -> {
      rewrite (is_list_seg_with pl prev cur endl p cs)
           as (is_list_seg_with pl prev cur endl p (c0 :: ct));
      seg_cons_elim pl prev cur endl p c0 ct;
      with v. assert (R.pts_to cur #p v);
      seg_pl_out pl cur (lnext v) endl p ct;
      rewrite (pl cur) as (pl c0);
      fold (payload_of pl (c0 :: ct));
      seg_cons_intro no_payload prev cur endl p c0 ct;
      rewrite (is_list_seg_with no_payload prev cur endl p (c0 :: ct)
               ** payload_of pl (c0 :: ct))
           as (is_list_seg_with no_payload prev cur endl p cs ** payload_of pl cs);
    }
  }
}

ghost
fn rec seg_pl_in (pl: payload) (prev cur endl: lref) (p: perm) (cs: list lref)
  requires is_list_seg_with no_payload prev cur endl p cs ** payload_of pl cs
  returns _: unit
  ensures is_list_seg_with pl prev cur endl p cs
  decreases cs
{
  match cs {
    Nil -> {
      rewrite (is_list_seg_with no_payload prev cur endl p cs ** payload_of pl cs)
           as (is_list_seg_with no_payload prev cur endl p (Nil #lref)
               ** payload_of pl (Nil #lref));
      seg_nil_elim no_payload prev cur endl p;
      unfold (payload_of pl (Nil #lref));
      seg_nil_intro pl prev cur endl p;
      rewrite (is_list_seg_with pl prev cur endl p (Nil #lref))
           as (is_list_seg_with pl prev cur endl p cs);
    }
    Cons c0 ct -> {
      rewrite (is_list_seg_with no_payload prev cur endl p cs ** payload_of pl cs)
           as (is_list_seg_with no_payload prev cur endl p (c0 :: ct)
               ** payload_of pl (c0 :: ct));
      unfold (payload_of pl (c0 :: ct));
      seg_cons_elim no_payload prev cur endl p c0 ct;
      with v. assert (R.pts_to cur #p v);
      seg_pl_in pl cur (lnext v) endl p ct;
      rewrite (pl c0) as (pl cur);
      seg_cons_intro pl prev cur endl p c0 ct;
      rewrite (is_list_seg_with pl prev cur endl p (c0 :: ct))
           as (is_list_seg_with pl prev cur endl p cs);
    }
  }
}

ghost
fn ring_pl_out (pl: payload) (head: lref) (p: perm) (cs: list lref)
  requires is_list_ring_with pl head p cs
  returns _: unit
  ensures is_list_ring_with no_payload head p cs ** payload_of pl cs
{
  unfold (is_list_ring_with pl head p cs);
  with hv. assert (R.pts_to head #p hv);
  seg_pl_out pl head (lnext hv) head p cs;
  fold (is_list_ring_with no_payload head p cs);
}

ghost
fn ring_pl_in (pl: payload) (head: lref) (p: perm) (cs: list lref)
  requires is_list_ring_with no_payload head p cs ** payload_of pl cs
  returns _: unit
  ensures is_list_ring_with pl head p cs
{
  unfold (is_list_ring_with no_payload head p cs);
  with hv. assert (R.pts_to head #p hv);
  seg_pl_in pl head (lnext hv) head p cs;
  fold (is_list_ring_with pl head p cs);
}

let first_or (d: lref) (cs: list lref) : Tot lref =
  match cs with
  | [] -> d
  | x :: _ -> x

let rec last_or_indep (d1 d2: lref) (cs: list lref)
  : Lemma (requires Cons? cs) (ensures last_or d1 cs == last_or d2 cs) (decreases cs)
  = match cs with
    | [_] -> ()
    | _ :: tl -> last_or_indep d1 d2 tl

let last_or_cons (d hd: lref) (tl: list lref)
  : Lemma (ensures last_or d (hd :: tl) == last_or hd tl)
  = match tl with
    | [] -> ()
    | _ -> last_or_indep d hd tl

let rec is_list_seg_s_with
    (pl: payload)
    (prev cur endl sent: lref)
    (p: perm)
    (cells: list lref)
  : Tot slprop (decreases cells)
  = match cells with
    | [] -> pure (cur == endl)
    | hd :: tl ->
      pure (cur == hd) **
      pure (cur =!= endl) **
      pure (cur =!= sent) **
      (exists* (v: L.struct_list_node).
        R.pts_to cur #p v **
        pl cur **
        pure (lprev v == prev) **
        is_list_seg_s_with pl cur (lnext v) endl sent p tl)

ghost
fn seg_head_distinct (pl: payload) (start sent mprev mcur: lref) (back: list lref)
                     (#v: L.struct_list_node)
  requires
    R.pts_to start #1.0R v **
    is_list_seg_with pl mprev mcur sent 1.0R back **
    pure (start =!= sent)
  returns _: unit
  ensures
    R.pts_to start #1.0R v **
    is_list_seg_with pl mprev mcur sent 1.0R back **
    pure (start =!= mcur)
{
  match back {
    Nil -> {
      unfold (is_list_seg_with pl mprev mcur sent 1.0R (Nil #lref));
      fold (is_list_seg_with pl mprev mcur sent 1.0R (Nil #lref));
      rewrite (is_list_seg_with pl mprev mcur sent 1.0R (Nil #lref))
           as (is_list_seg_with pl mprev mcur sent 1.0R back);
    }
    Cons b bt -> {
      unfold (is_list_seg_with pl mprev mcur sent 1.0R (b :: bt));
      with vb. assert (R.pts_to mcur #1.0R vb);
      refs_distinct start mcur;
      fold (is_list_seg_with pl mprev mcur sent 1.0R (b :: bt));
      rewrite (is_list_seg_with pl mprev mcur sent 1.0R (b :: bt))
           as (is_list_seg_with pl mprev mcur sent 1.0R back);
    }
  }
}

ghost
fn rec seg_split (pl: payload) (prev start sent: lref) (front back: list lref)
  requires is_list_seg_with pl prev start sent 1.0R (front @ back)
  returns _: unit
  ensures
    exists* (mcur: lref).
      is_list_seg_s_with pl prev start mcur sent 1.0R front **
      is_list_seg_with pl (last_or prev front) mcur sent 1.0R back
  decreases front
{
  match front {
    Nil -> {
      rewrite (is_list_seg_with pl prev start sent 1.0R ([] @ back))
           as (is_list_seg_with pl prev start sent 1.0R back);
      fold (is_list_seg_s_with pl prev start start sent 1.0R (Nil #lref));
      rewrite (is_list_seg_s_with pl prev start start sent 1.0R (Nil #lref))
           as (is_list_seg_s_with pl prev start start sent 1.0R front);
      rewrite (is_list_seg_with pl prev start sent 1.0R back)
           as (is_list_seg_with pl (last_or prev front) start sent 1.0R back);
    }
    Cons hd tl -> {
      rewrite (is_list_seg_with pl prev start sent 1.0R ((hd :: tl) @ back))
           as (is_list_seg_with pl prev start sent 1.0R (hd :: (tl @ back)));
      unfold (is_list_seg_with pl prev start sent 1.0R (hd :: (tl @ back)));
      with v. assert (R.pts_to start #1.0R v);
      seg_split pl start (lnext v) sent tl back;
      with mcur. assert (is_list_seg_s_with pl start (lnext v) mcur sent 1.0R tl);
      seg_head_distinct pl start sent (last_or start tl) mcur back;
      fold (is_list_seg_s_with pl prev start mcur sent 1.0R (hd :: tl));
      last_or_cons prev hd tl;
      rewrite (is_list_seg_with pl (last_or start tl) mcur sent 1.0R back)
           as (is_list_seg_with pl (last_or prev front) mcur sent 1.0R back);
      rewrite (is_list_seg_s_with pl prev start mcur sent 1.0R (hd :: tl))
           as (is_list_seg_s_with pl prev start mcur sent 1.0R front);
    }
  }
}

ghost
fn rec seg_merge (pl: payload) (prev start mcur sent: lref) (front back: list lref)
  requires
    is_list_seg_s_with pl prev start mcur sent 1.0R front **
    is_list_seg_with pl (last_or prev front) mcur sent 1.0R back
  returns _: unit
  ensures is_list_seg_with pl prev start sent 1.0R (front @ back)
  decreases front
{
  match front {
    Nil -> {
      unfold (is_list_seg_s_with pl prev start mcur sent 1.0R (Nil #lref));
      rewrite (is_list_seg_with pl (last_or prev (Nil #lref)) mcur sent 1.0R back)
           as (is_list_seg_with pl prev start sent 1.0R (front @ back));
    }
    Cons hd tl -> {
      unfold (is_list_seg_s_with pl prev start mcur sent 1.0R (hd :: tl));
      with v. assert (R.pts_to start #1.0R v);
      last_or_cons prev hd tl;
      rewrite (is_list_seg_with pl (last_or prev (hd :: tl)) mcur sent 1.0R back)
           as (is_list_seg_with pl (last_or start tl) mcur sent 1.0R back);
      seg_merge pl start (lnext v) mcur sent tl back;
      fold (is_list_seg_with pl prev start sent 1.0R (hd :: (tl @ back)));
      rewrite (is_list_seg_with pl prev start sent 1.0R (hd :: (tl @ back)))
           as (is_list_seg_with pl prev start sent 1.0R (front @ back));
    }
  }
}

let add_pre (al: bool) (nw prev next: lref) (vp vx: L.struct_list_node) : slprop =
  (exists* (vn: L.struct_list_node). R.pts_to nw #1.0R vn) **
  (if al
   then pure (prev == next /\ vp == vx) ** R.pts_to prev #1.0R vp
   else pure (prev =!= next) ** R.pts_to prev #1.0R vp ** R.pts_to next #1.0R vx)

let add_post (al: bool) (nw prev next: lref) (vp vx: L.struct_list_node) : slprop =
  R.pts_to nw #1.0R (mklink next prev) **
  (if al
   then R.pts_to prev #1.0R (mklink nw nw)
   else R.pts_to prev #1.0R ({ vp with L.struct_list_node__next = nw }) **
        R.pts_to next #1.0R ({ vx with L.struct_list_node__prev = nw }))

ghost
fn ring_open (pl: payload) (head: lref) (#p: perm) (#cells: list lref)
  requires is_list_ring_with pl head p cells
  returns _: unit
  ensures
    exists* (hv: L.struct_list_node).
      R.pts_to head #p hv **
      is_list_seg_with pl head (lnext hv) head p cells **
      pure (lprev hv == last_or head cells) **
      pure ((lnext hv == head) <==> (cells == []))
{
  unfold (is_list_ring_with pl head p cells);
  with hv. assert (R.pts_to head #p hv);

  if (Nil? cells) {
    rewrite (is_list_seg_with pl head (lnext hv) head p cells)
         as (is_list_seg_with pl head (lnext hv) head p (Nil #lref));
    unfold (is_list_seg_with pl head (lnext hv) head p (Nil #lref));
    fold (is_list_seg_with pl head (lnext hv) head p (Nil #lref));
    rewrite (is_list_seg_with pl head (lnext hv) head p (Nil #lref))
         as (is_list_seg_with pl head (lnext hv) head p cells);
  } else {
    let hd = Cons?.hd cells;
    let tl = Cons?.tl cells;
    rewrite (is_list_seg_with pl head (lnext hv) head p cells)
         as (is_list_seg_with pl head (lnext hv) head p (hd :: tl));
    unfold (is_list_seg_with pl head (lnext hv) head p (hd :: tl));
    fold (is_list_seg_with pl head (lnext hv) head p (hd :: tl));
    rewrite (is_list_seg_with pl head (lnext hv) head p (hd :: tl))
         as (is_list_seg_with pl head (lnext hv) head p cells);
  }
}

ghost
fn seg_first (pl: payload) (prev cur endl: lref) (#p: perm) (#cells: list lref)
  requires is_list_seg_with pl prev cur endl p cells
  returns _: unit
  ensures is_list_seg_with pl prev cur endl p cells **
          pure (cur == first_or endl cells)
{
  if (Nil? cells) {
    rewrite (is_list_seg_with pl prev cur endl p cells)
         as (is_list_seg_with pl prev cur endl p (Nil #lref));
    unfold (is_list_seg_with pl prev cur endl p (Nil #lref));
    fold (is_list_seg_with pl prev cur endl p (Nil #lref));
    rewrite (is_list_seg_with pl prev cur endl p (Nil #lref))
         as (is_list_seg_with pl prev cur endl p cells);
  } else {
    let hd = Cons?.hd cells;
    let tl = Cons?.tl cells;
    rewrite (is_list_seg_with pl prev cur endl p cells)
         as (is_list_seg_with pl prev cur endl p (hd :: tl));
    unfold (is_list_seg_with pl prev cur endl p (hd :: tl));
    fold (is_list_seg_with pl prev cur endl p (hd :: tl));
    rewrite (is_list_seg_with pl prev cur endl p (hd :: tl))
         as (is_list_seg_with pl prev cur endl p cells);
  }
}

ghost
fn rec seg_last_ne (pl: payload) (prev cur endl: lref) (#p: perm) (#cells: list lref)
  requires is_list_seg_with pl prev cur endl p cells
  returns _: unit
  ensures is_list_seg_with pl prev cur endl p cells **
          pure ((last_or endl cells == endl) <==> (cells == []))
  decreases cells
{
  if (Nil? cells) {
    rewrite (is_list_seg_with pl prev cur endl p cells)
         as (is_list_seg_with pl prev cur endl p (Nil #lref));
    unfold (is_list_seg_with pl prev cur endl p (Nil #lref));
    fold (is_list_seg_with pl prev cur endl p (Nil #lref));
    rewrite (is_list_seg_with pl prev cur endl p (Nil #lref))
         as (is_list_seg_with pl prev cur endl p cells);
  } else {
    let hd = Cons?.hd cells;
    let tl = Cons?.tl cells;
    rewrite (is_list_seg_with pl prev cur endl p cells)
         as (is_list_seg_with pl prev cur endl p (hd :: tl));
    seg_cons_elim pl prev cur endl p hd tl;
    with vc. assert (R.pts_to cur #p vc);
    seg_last_ne pl cur (lnext vc) endl;
    last_or_cons endl hd tl;
    seg_cons_intro pl prev cur endl p hd tl;
    rewrite (is_list_seg_with pl prev cur endl p (hd :: tl))
         as (is_list_seg_with pl prev cur endl p cells);
  }
}

ghost
fn ring_open_full (pl: payload) (head: lref) (#p: perm) (#cells: list lref)
  requires is_list_ring_with pl head p cells
  returns _: unit
  ensures
    exists* (hv: L.struct_list_node).
      R.pts_to head #p hv **
      is_list_seg_with pl head (lnext hv) head p cells **
      pure (lprev hv == last_or head cells) **
      pure (lnext hv == first_or head cells) **
      pure ((lnext hv == head) <==> (cells == [])) **
      pure ((lprev hv == head) <==> (cells == []))
{
  ring_open pl head;
  with hv. assert (R.pts_to head #p hv);
  seg_first pl head (lnext hv) head;
  seg_last_ne pl head (lnext hv) head;
}

ghost
fn ring_close (pl: payload) (head: lref) (#p: perm) (#cells: list lref)
              (#hv: L.struct_list_node)
  requires
    R.pts_to head #p hv **
    is_list_seg_with pl head (lnext hv) head p cells **
    pure (lprev hv == last_or head cells)
  returns _: unit
  ensures is_list_ring_with pl head p cells
{
  fold (is_list_ring_with pl head p cells);
}

ghost
fn rec seg_last_distinct (pl: payload) (prev cur endl x: lref) (cs: list lref)
                         (#v: L.struct_list_node)
  requires
    R.pts_to x #1.0R v **
    is_list_seg_with pl prev cur endl 1.0R cs **
    pure (Cons? cs)
  returns _: unit
  ensures
    R.pts_to x #1.0R v **
    is_list_seg_with pl prev cur endl 1.0R cs **
    pure (x =!= last_or prev cs)
  decreases cs
{
  let hd = Cons?.hd cs;
  let tl = Cons?.tl cs;
  rewrite (is_list_seg_with pl prev cur endl 1.0R cs)
       as (is_list_seg_with pl prev cur endl 1.0R (hd :: tl));
  seg_cons_elim pl prev cur endl 1.0R hd tl;
  with vc. assert (R.pts_to cur #1.0R vc);
  refs_distinct x cur;
  last_or_cons prev hd tl;

  if (Nil? tl) {

    seg_cons_intro pl prev cur endl 1.0R hd tl;
    rewrite (is_list_seg_with pl prev cur endl 1.0R (hd :: tl))
         as (is_list_seg_with pl prev cur endl 1.0R cs);
  } else {
    seg_last_distinct pl cur (lnext vc) endl x tl;
    last_or_indep cur hd tl;
    seg_cons_intro pl prev cur endl 1.0R hd tl;
    rewrite (is_list_seg_with pl prev cur endl 1.0R (hd :: tl))
         as (is_list_seg_with pl prev cur endl 1.0R cs);
  }
}

ghost
fn ring_ends_iff (pl: payload) (head: lref) (#cells: list lref) (#hv: L.struct_list_node)
  requires
    R.pts_to head #1.0R hv **
    is_list_seg_with pl head (lnext hv) head 1.0R cells **
    pure (lprev hv == last_or head cells)
  returns _: unit
  ensures
    R.pts_to head #1.0R hv **
    is_list_seg_with pl head (lnext hv) head 1.0R cells **
    pure (lprev hv == last_or head cells) **
    pure ((Cons? cells /\ lnext hv == lprev hv) <==> (length cells == 1))
{
  if (Nil? cells) {
    ()
  } else {
    let hd = Cons?.hd cells;
    let tl = Cons?.tl cells;
    rewrite (is_list_seg_with pl head (lnext hv) head 1.0R cells)
         as (is_list_seg_with pl head (lnext hv) head 1.0R (hd :: tl));
    seg_cons_elim pl head (lnext hv) head 1.0R hd tl;
    with vc. assert (R.pts_to (lnext hv) #1.0R vc);
    last_or_cons head hd tl;

    if (Nil? tl) {

      seg_cons_intro pl head (lnext hv) head 1.0R hd tl;
      rewrite (is_list_seg_with pl head (lnext hv) head 1.0R (hd :: tl))
           as (is_list_seg_with pl head (lnext hv) head 1.0R cells);
    } else {

      seg_last_distinct pl (lnext hv) (lnext vc) head (lnext hv) tl;
      last_or_indep (lnext hv) hd tl;
      seg_cons_intro pl head (lnext hv) head 1.0R hd tl;
      rewrite (is_list_seg_with pl head (lnext hv) head 1.0R (hd :: tl))
           as (is_list_seg_with pl head (lnext hv) head 1.0R cells);
    }
  }
}

let is_list_split_with
    (pl: payload) (head: lref) (p: perm)
    (prev next: lref) (front back: list lref)
  : slprop
  = exists* (hv: L.struct_list_node).
      R.pts_to head #p hv **
      is_list_seg_s_with pl head (lnext hv) next head p front **
      is_list_seg_with pl prev next head p back **
      pure (prev == last_or head front) **
      pure (lprev hv == last_or head (front @ back))

unfold let is_list_split (head: lref) (p: perm) (prev next: lref)
                         (front back: list lref) : slprop =
  is_list_split_with no_payload head p prev next front back

ghost
fn split_open (pl: payload) (head: lref) (front back: list lref)
  requires is_list_ring_with pl head 1.0R (front @ back)
  returns _: unit
  ensures
    exists* (next: lref).
      is_list_split_with pl head 1.0R (last_or head front) next front back
{
  ring_open pl head;
  with hv. assert (R.pts_to head #1.0R hv);
  seg_split pl head (lnext hv) head front back;
  with mcur. assert (is_list_seg_s_with pl head (lnext hv) mcur head 1.0R front);
  fold (is_list_split_with pl head 1.0R (last_or head front) mcur front back);
}

ghost
fn split_close (pl: payload) (head: lref) (prev next: lref) (front back: list lref)
  requires is_list_split_with pl head 1.0R prev next front back
  returns _: unit
  ensures is_list_ring_with pl head 1.0R (front @ back)
{
  unfold (is_list_split_with pl head 1.0R prev next front back);
  with hv. assert (R.pts_to head #1.0R hv);
  rewrite (is_list_seg_with pl prev next head 1.0R back)
       as (is_list_seg_with pl (last_or head front) next head 1.0R back);
  seg_merge pl head (lnext hv) next head front back;
  ring_close pl head;
}

ghost
fn rec seg_s_pl_out (pl: payload) (prev cur endl sent: lref) (p: perm) (cs: list lref)
  requires is_list_seg_s_with pl prev cur endl sent p cs
  returns _: unit
  ensures is_list_seg_s_with no_payload prev cur endl sent p cs ** payload_of pl cs
  decreases cs
{
  match cs {
    Nil -> {
      rewrite (is_list_seg_s_with pl prev cur endl sent p cs)
           as (is_list_seg_s_with pl prev cur endl sent p (Nil #lref));
      unfold (is_list_seg_s_with pl prev cur endl sent p (Nil #lref));
      fold (is_list_seg_s_with no_payload prev cur endl sent p (Nil #lref));
      fold (payload_of pl (Nil #lref));
      rewrite (is_list_seg_s_with no_payload prev cur endl sent p (Nil #lref)
               ** payload_of pl (Nil #lref))
           as (is_list_seg_s_with no_payload prev cur endl sent p cs ** payload_of pl cs);
    }
    Cons c0 ct -> {
      rewrite (is_list_seg_s_with pl prev cur endl sent p cs)
           as (is_list_seg_s_with pl prev cur endl sent p (c0 :: ct));
      unfold (is_list_seg_s_with pl prev cur endl sent p (c0 :: ct));
      with v. assert (R.pts_to cur #p v);
      seg_s_pl_out pl cur (lnext v) endl sent p ct;
      rewrite (pl cur) as (pl c0);
      fold (payload_of pl (c0 :: ct));
      fold (is_list_seg_s_with no_payload prev cur endl sent p (c0 :: ct));
      rewrite (is_list_seg_s_with no_payload prev cur endl sent p (c0 :: ct)
               ** payload_of pl (c0 :: ct))
           as (is_list_seg_s_with no_payload prev cur endl sent p cs ** payload_of pl cs);
    }
  }
}

ghost
fn rec seg_s_pl_in (pl: payload) (prev cur endl sent: lref) (p: perm) (cs: list lref)
  requires is_list_seg_s_with no_payload prev cur endl sent p cs ** payload_of pl cs
  returns _: unit
  ensures is_list_seg_s_with pl prev cur endl sent p cs
  decreases cs
{
  match cs {
    Nil -> {
      rewrite (is_list_seg_s_with no_payload prev cur endl sent p cs ** payload_of pl cs)
           as (is_list_seg_s_with no_payload prev cur endl sent p (Nil #lref)
               ** payload_of pl (Nil #lref));
      unfold (is_list_seg_s_with no_payload prev cur endl sent p (Nil #lref));
      unfold (payload_of pl (Nil #lref));
      fold (is_list_seg_s_with pl prev cur endl sent p (Nil #lref));
      rewrite (is_list_seg_s_with pl prev cur endl sent p (Nil #lref))
           as (is_list_seg_s_with pl prev cur endl sent p cs);
    }
    Cons c0 ct -> {
      rewrite (is_list_seg_s_with no_payload prev cur endl sent p cs ** payload_of pl cs)
           as (is_list_seg_s_with no_payload prev cur endl sent p (c0 :: ct)
               ** payload_of pl (c0 :: ct));
      unfold (payload_of pl (c0 :: ct));
      unfold (is_list_seg_s_with no_payload prev cur endl sent p (c0 :: ct));
      with v. assert (R.pts_to cur #p v);
      seg_s_pl_in pl cur (lnext v) endl sent p ct;
      rewrite (pl c0) as (pl cur);
      fold (is_list_seg_s_with pl prev cur endl sent p (c0 :: ct));
      rewrite (is_list_seg_s_with pl prev cur endl sent p (c0 :: ct))
           as (is_list_seg_s_with pl prev cur endl sent p cs);
    }
  }
}

ghost
fn split_pl_out (pl: payload) (head: lref) (p: perm) (prev next: lref)
                (front back: list lref)
  requires is_list_split_with pl head p prev next front back
  returns _: unit
  ensures is_list_split_with no_payload head p prev next front back
       ** payload_of pl (front @ back)
{
  unfold (is_list_split_with pl head p prev next front back);
  with hv. assert (R.pts_to head #p hv);
  seg_s_pl_out pl head (lnext hv) next head p front;
  seg_pl_out pl prev next head p back;
  payload_of_join pl front back;
  fold (is_list_split_with no_payload head p prev next front back);
}

ghost
fn split_pl_in (pl: payload) (head: lref) (p: perm) (prev next: lref)
               (front back: list lref)
  requires is_list_split_with no_payload head p prev next front back
        ** payload_of pl (front @ back)
  returns _: unit
  ensures is_list_split_with pl head p prev next front back
{
  unfold (is_list_split_with no_payload head p prev next front back);
  with hv. assert (R.pts_to head #p hv);
  payload_of_split pl front back;
  seg_s_pl_in pl head (lnext hv) next head p front;
  seg_pl_in pl prev next head p back;
  fold (is_list_split_with pl head p prev next front back);
}

ghost
fn rec seg_s_peel_last (pl: payload) (prev start endl sent: lref)
                       (front': list lref) (lst: lref)
  requires is_list_seg_s_with pl prev start endl sent 1.0R (front' @ [lst])
  returns _: unit
  ensures
    exists* (vl: L.struct_list_node).
      is_list_seg_s_with pl prev start lst sent 1.0R front' **
      R.pts_to lst #1.0R vl **
      pl lst **
      pure (lnext vl == endl) **
      pure (lprev vl == last_or prev front') **
      pure (lst =!= endl) **
      pure (lst =!= sent)
  decreases front'
{
  match front' {
    Nil -> {
      rewrite (is_list_seg_s_with pl prev start endl sent 1.0R (front' @ [lst]))
           as (is_list_seg_s_with pl prev start endl sent 1.0R (lst :: []));
      unfold (is_list_seg_s_with pl prev start endl sent 1.0R (lst :: []));
      with vl. assert (R.pts_to start #1.0R vl);
      unfold (is_list_seg_s_with pl start (lnext vl) endl sent 1.0R (Nil #lref));
      rewrite (R.pts_to start #1.0R vl) as (R.pts_to lst #1.0R vl);
      rewrite (pl start) as (pl lst);
      fold (is_list_seg_s_with pl prev start lst sent 1.0R (Nil #lref));
      rewrite (is_list_seg_s_with pl prev start lst sent 1.0R (Nil #lref))
           as (is_list_seg_s_with pl prev start lst sent 1.0R front');
    }
    Cons f0 ft -> {
      rewrite (is_list_seg_s_with pl prev start endl sent 1.0R (front' @ [lst]))
           as (is_list_seg_s_with pl prev start endl sent 1.0R (f0 :: (ft @ [lst])));
      unfold (is_list_seg_s_with pl prev start endl sent 1.0R (f0 :: (ft @ [lst])));
      with v0. assert (R.pts_to start #1.0R v0);
      seg_s_peel_last pl start (lnext v0) endl sent ft lst;
      with vl. assert (R.pts_to lst #1.0R vl);

      refs_distinct start lst;
      last_or_cons prev f0 ft;
      fold (is_list_seg_s_with pl prev start lst sent 1.0R (f0 :: ft));
      rewrite (is_list_seg_s_with pl prev start lst sent 1.0R (f0 :: ft))
           as (is_list_seg_s_with pl prev start lst sent 1.0R front');
    }
  }
}

ghost
fn rec seg_s_snoc (pl: payload) (prev start sent: lref)
                  (front': list lref) (lst: lref)
                  (#vl: L.struct_list_node) (#ve: L.struct_list_node)
  requires
    is_list_seg_s_with pl prev start lst sent 1.0R front' **
    R.pts_to lst #1.0R vl **
    pl lst **
    R.pts_to (lnext vl) #1.0R ve **
    pure (lprev vl == last_or prev front') **
    pure (lst =!= sent)
  returns _: unit
  ensures
    is_list_seg_s_with pl prev start (lnext vl) sent 1.0R (front' @ [lst]) **
    R.pts_to (lnext vl) #1.0R ve
  decreases front'
{

  refs_distinct lst (lnext vl);
  match front' {
    Nil -> {
      rewrite (is_list_seg_s_with pl prev start lst sent 1.0R front')
           as (is_list_seg_s_with pl prev start lst sent 1.0R (Nil #lref));
      unfold (is_list_seg_s_with pl prev start lst sent 1.0R (Nil #lref));
      rewrite (R.pts_to lst #1.0R vl) as (R.pts_to start #1.0R vl);
      rewrite (pl lst) as (pl start);
      fold (is_list_seg_s_with pl start (lnext vl) (lnext vl) sent 1.0R (Nil #lref));
      fold (is_list_seg_s_with pl prev start (lnext vl) sent 1.0R (lst :: []));
      rewrite (is_list_seg_s_with pl prev start (lnext vl) sent 1.0R (lst :: []))
           as (is_list_seg_s_with pl prev start (lnext vl) sent 1.0R (front' @ [lst]));
    }
    Cons f0 ft -> {
      rewrite (is_list_seg_s_with pl prev start lst sent 1.0R front')
           as (is_list_seg_s_with pl prev start lst sent 1.0R (f0 :: ft));
      unfold (is_list_seg_s_with pl prev start lst sent 1.0R (f0 :: ft));
      with v0. assert (R.pts_to start #1.0R v0);
      refs_distinct start (lnext vl);
      last_or_cons prev f0 ft;
      seg_s_snoc pl start (lnext v0) sent ft lst;
      fold (is_list_seg_s_with pl prev start (lnext vl) sent 1.0R (f0 :: (ft @ [lst])));
      rewrite (is_list_seg_s_with pl prev start (lnext vl) sent 1.0R (f0 :: (ft @ [lst])))
           as (is_list_seg_s_with pl prev start (lnext vl) sent 1.0R (front' @ [lst]));
    }
  }
}

unfold let is_list_seg_s (prev cur endl sent: lref) (p: perm) (cells: list lref) : slprop =
  is_list_seg_s_with no_payload prev cur endl sent p cells

let rec last_or_append_cons (d: lref) (xs: list lref) (ys: list lref)
  : Lemma (requires Cons? ys) (ensures last_or d (xs @ ys) == last_or d ys)
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: xt ->
      last_or_append_cons d xt ys;
      last_or_cons d x (xt @ ys);
      last_or_indep d x ys;
      (match xt @ ys with
       | _ :: _ -> last_or_indep x d (xt @ ys)
       | [] -> ())

let rec last_or_snoc (d: lref) (l: list lref) (x: lref)
  : Lemma (ensures last_or d (l @ [x]) == x) (decreases l)
  = match l with
    | [] -> ()
    | _ :: tl -> last_or_snoc d tl x

ghost
fn seg_cur_ne (pl: payload) (prev cur endl: lref) (#p: perm) (#cells: list lref)
  requires is_list_seg_with pl prev cur endl p cells
  returns _: unit
  ensures is_list_seg_with pl prev cur endl p cells **
          pure ((cur == endl) <==> (cells == []))
{
  if (Nil? cells) {
    rewrite (is_list_seg_with pl prev cur endl p cells)
         as (is_list_seg_with pl prev cur endl p (Nil #lref));
    unfold (is_list_seg_with pl prev cur endl p (Nil #lref));
    fold (is_list_seg_with pl prev cur endl p (Nil #lref));
    rewrite (is_list_seg_with pl prev cur endl p (Nil #lref))
         as (is_list_seg_with pl prev cur endl p cells);
  } else {
    let hd = Cons?.hd cells;
    let tl = Cons?.tl cells;
    rewrite (is_list_seg_with pl prev cur endl p cells)
         as (is_list_seg_with pl prev cur endl p (hd :: tl));
    unfold (is_list_seg_with pl prev cur endl p (hd :: tl));
    fold (is_list_seg_with pl prev cur endl p (hd :: tl));
    rewrite (is_list_seg_with pl prev cur endl p (hd :: tl))
         as (is_list_seg_with pl prev cur endl p cells);
  }
}

let iter_rest (pl: payload) (head prev next: lref)
              (front: list lref) (b0: lref) (bt: list lref) (nx: lref) : slprop =
  exists* (hv: L.struct_list_node).
    R.pts_to head #1.0R hv **
    is_list_seg_s_with pl head (lnext hv) next head 1.0R front **
    is_list_seg_with pl next nx head 1.0R bt **
    pure (next == b0) **
    pure (next =!= head) **
    pure (prev == last_or head front) **
    pure (lprev hv == last_or head (front @ (b0 :: bt)))

ghost
fn iter_expose (pl: payload) (head prev next: lref)
               (front: list lref) (b0: lref) (bt: list lref)
  requires is_list_split_with pl head 1.0R prev next front (b0 :: bt)
  returns _: unit
  ensures
    exists* (vn: L.struct_list_node).
      R.pts_to next #1.0R vn **
      pl next **
      iter_rest pl head prev next front b0 bt (lnext vn) **
      pure (lprev vn == prev) **
      pure (next == b0) **
      pure (next =!= head)
{
  unfold (is_list_split_with pl head 1.0R prev next front (b0 :: bt));
  seg_cons_elim pl prev next head 1.0R b0 bt;
  with vn. assert (R.pts_to next #1.0R vn);
  fold (iter_rest pl head prev next front b0 bt (lnext vn));
}

ghost
fn iter_unexpose (pl: payload) (head prev next: lref)
                 (front: list lref) (b0: lref) (bt: list lref)
                 (#vn: L.struct_list_node)
  requires
    R.pts_to next #1.0R vn **
    pl next **
    iter_rest pl head prev next front b0 bt (lnext vn) **
    pure (lprev vn == prev)
  returns _: unit
  ensures is_list_split_with pl head 1.0R prev next front (b0 :: bt)
{
  unfold (iter_rest pl head prev next front b0 bt (lnext vn));
  seg_cons_intro pl prev next head 1.0R b0 bt;
  fold (is_list_split_with pl head 1.0R prev next front (b0 :: bt));
}

ghost
fn iter_advance (pl: payload) (head prev next: lref)
                (front: list lref) (b0: lref) (bt: list lref)
                (#vn: L.struct_list_node)
  requires
    R.pts_to next #1.0R vn **
    pl next **
    iter_rest pl head prev next front b0 bt (lnext vn) **
    pure (lprev vn == prev)
  returns _: unit
  ensures is_list_split_with pl head 1.0R next (lnext vn) (front @ [next]) bt
{
  unfold (iter_rest pl head prev next front b0 bt (lnext vn));
  with hv. assert (R.pts_to head #1.0R hv);
  last_or_snoc head front next;
  FStar.List.Tot.Properties.append_assoc front [next] bt;
  match bt {
    Nil -> {

      rewrite (is_list_seg_with pl next (lnext vn) head 1.0R bt)
           as (is_list_seg_with pl next (lnext vn) head 1.0R (Nil #lref));
      seg_nil_elim pl next (lnext vn) head 1.0R;
      rewrite (R.pts_to head #1.0R hv) as (R.pts_to (lnext vn) #1.0R hv);
      seg_s_snoc pl head (lnext hv) head front next;
      rewrite (R.pts_to (lnext vn) #1.0R hv) as (R.pts_to head #1.0R hv);
      seg_nil_intro pl next (lnext vn) head 1.0R;
      rewrite (is_list_seg_with pl next (lnext vn) head 1.0R (Nil #lref))
           as (is_list_seg_with pl next (lnext vn) head 1.0R bt);
      fold (is_list_split_with pl head 1.0R next (lnext vn) (front @ [next]) bt);
    }
    Cons c0 ct -> {

      rewrite (is_list_seg_with pl next (lnext vn) head 1.0R bt)
           as (is_list_seg_with pl next (lnext vn) head 1.0R (c0 :: ct));
      seg_cons_elim pl next (lnext vn) head 1.0R c0 ct;
      seg_s_snoc pl head (lnext hv) head front next;
      seg_cons_intro pl next (lnext vn) head 1.0R c0 ct;
      rewrite (is_list_seg_with pl next (lnext vn) head 1.0R (c0 :: ct))
           as (is_list_seg_with pl next (lnext vn) head 1.0R bt);
      fold (is_list_split_with pl head 1.0R next (lnext vn) (front @ [next]) bt);
    }
  }
}

ghost
fn split_cur_ne (pl: payload) (head prev next: lref) (front back: list lref)
  requires is_list_split_with pl head 1.0R prev next front back
  returns _: unit
  ensures is_list_split_with pl head 1.0R prev next front back **
          pure ((next == head) <==> (back == []))
{
  unfold (is_list_split_with pl head 1.0R prev next front back);
  seg_cur_ne pl prev next head;
  fold (is_list_split_with pl head 1.0R prev next front back);
}

let add_rest1 (head prev next: lref) (front back: list lref) (nx: lref) : slprop =
  match back with
  | [] ->
    is_list_seg_s head nx next head 1.0R front **
    pure (next == head) **
    pure (prev == last_or head front)
  | b0 :: bt ->
    exists* (hv: L.struct_list_node).
      R.pts_to head #1.0R hv **
      is_list_seg_s head (lnext hv) next head 1.0R front **
      is_list_seg next nx head 1.0R bt **
      pure (next == b0) **
      pure (next =!= head) **
      pure (prev == last_or head front) **
      pure (lprev hv == last_or head (front @ back))

ghost
fn add_expose_next (head prev next: lref) (front back: list lref)
  requires is_list_split head 1.0R prev next front back
  returns _: unit
  ensures
    exists* (vn: L.struct_list_node).
      R.pts_to next #1.0R vn **
      add_rest1 head prev next front back (lnext vn)
{
  unfold (is_list_split_with no_payload head 1.0R prev next front back);
  with hv. assert (R.pts_to head #1.0R hv);
  match back {
    Nil -> {
      rewrite (is_list_seg_with no_payload prev next head 1.0R back)
           as (is_list_seg_with no_payload prev next head 1.0R (Nil #lref));
      seg_nil_elim no_payload prev next head 1.0R;
      rewrite (R.pts_to head #1.0R hv) as (R.pts_to next #1.0R hv);
      rewrite (is_list_seg_s_with no_payload head (lnext hv) next head 1.0R front)
           as (is_list_seg_s head (lnext hv) next head 1.0R front);
      fold (add_rest1 head prev next front (Nil #lref) (lnext hv));
      rewrite (add_rest1 head prev next front (Nil #lref) (lnext hv))
           as (add_rest1 head prev next front back (lnext hv));
    }
    Cons b0 bt -> {
      rewrite (is_list_seg_with no_payload prev next head 1.0R back)
           as (is_list_seg_with no_payload prev next head 1.0R (b0 :: bt));
      seg_cons_elim no_payload prev next head 1.0R b0 bt;
      with vn. assert (R.pts_to next #1.0R vn);
      fold (add_rest1 head prev next front (b0 :: bt) (lnext vn));
      rewrite (add_rest1 head prev next front (b0 :: bt) (lnext vn))
           as (add_rest1 head prev next front back (lnext vn));
    }
  }
}

let finit (l: list lref { Cons? l }) : list lref = FStar.List.Tot.init l
let flast (l: list lref { Cons? l }) : lref = FStar.List.Tot.last l

let rec finit_flast_append (l: list lref { Cons? l })
  : Lemma (ensures finit l @ [flast l] == l) (decreases l)
  = match l with
    | [_] -> ()
    | _ :: tl -> finit_flast_append tl

let rec last_or_flast (d: lref) (l: list lref { Cons? l })
  : Lemma (ensures last_or d l == flast l) (decreases l)
  = match l with
    | [_] -> ()
    | _ :: tl -> last_or_flast d tl

let add_rest2 (head prev next: lref) (front back: list lref) (nw nx pp: lref) : slprop =
  match front, back with
  | [], [] ->
    pure (prev == head /\ next == head /\ nx == head /\ pp == nw)
  | [], b0 :: bt ->
    exists* (vn: L.struct_list_node).
      R.pts_to next #1.0R vn **
      is_list_seg next nx head 1.0R bt **
      pure (prev == head /\ next == b0 /\ next =!= head) **
      pure (lprev vn == nw /\ lnext vn == nx) **
      pure (pp == last_or head back)
  | f0 :: ft, [] ->
    exists* (vh: L.struct_list_node).
      R.pts_to head #1.0R vh **
      is_list_seg_s head (lnext vh) prev head 1.0R (finit (f0 :: ft)) **
      pure (next == head /\ prev == flast (f0 :: ft) /\ prev =!= head) **
      pure (lprev vh == nw /\ lnext vh == nx) **
      pure (pp == last_or head (finit (f0 :: ft)))
  | f0 :: ft, b0 :: bt ->
    exists* (vh: L.struct_list_node) (vn: L.struct_list_node).
      R.pts_to head #1.0R vh **
      R.pts_to next #1.0R vn **
      is_list_seg_s head (lnext vh) prev head 1.0R (finit (f0 :: ft)) **
      is_list_seg next nx head 1.0R bt **
      pure (prev == flast (f0 :: ft) /\ prev =!= head) **
      pure (next == b0 /\ next =!= head) **
      pure (lprev vn == nw /\ lnext vn == nx) **
      pure (lprev vh == last_or head (front @ back)) **
      pure (pp == last_or head (finit (f0 :: ft)))

ghost
fn add_reseat (head prev next nw: lref) (front back: list lref) (#nx: lref)
              (#vn: L.struct_list_node)
  requires
    R.pts_to next #1.0R vn **
    add_rest1 head prev next front back nx **
    pure (lprev vn == nw) **
    pure (lnext vn == nx)
  returns _: unit
  ensures
    exists* (vp: L.struct_list_node).
      R.pts_to prev #1.0R vp **
      add_rest2 head prev next front back nw nx (lprev vp) **
      pure (lnext vp == next)
{
  match front {
    Nil -> {
      match back {
        Nil -> {

          rewrite (add_rest1 head prev next front back nx)
               as (add_rest1 head prev next (Nil #lref) (Nil #lref) nx);
          unfold (add_rest1 head prev next (Nil #lref) (Nil #lref) nx);
          unfold (is_list_seg_s_with no_payload head nx next head 1.0R (Nil #lref));
          rewrite (R.pts_to next #1.0R vn) as (R.pts_to prev #1.0R vn);
          fold (add_rest2 head prev next (Nil #lref) (Nil #lref) nw nx (lprev vn));
          rewrite (add_rest2 head prev next (Nil #lref) (Nil #lref) nw nx (lprev vn))
               as (add_rest2 head prev next front back nw nx (lprev vn));
        }
        Cons b0 bt -> {

          rewrite (add_rest1 head prev next front back nx)
               as (add_rest1 head prev next (Nil #lref) (b0 :: bt) nx);
          unfold (add_rest1 head prev next (Nil #lref) (b0 :: bt) nx);
          with hv. assert (R.pts_to head #1.0R hv);
          unfold (is_list_seg_s_with no_payload head (lnext hv) next head 1.0R (Nil #lref));
          rewrite (R.pts_to head #1.0R hv) as (R.pts_to prev #1.0R hv);
          fold (add_rest2 head prev next (Nil #lref) (b0 :: bt) nw nx (lprev hv));
          rewrite (add_rest2 head prev next (Nil #lref) (b0 :: bt) nw nx (lprev hv))
               as (add_rest2 head prev next front back nw nx (lprev hv));
        }
      }
    }
    Cons f0 ft -> {
      last_or_flast head front;
      finit_flast_append front;
      match back {
        Nil -> {

          rewrite (add_rest1 head prev next front back nx)
               as (add_rest1 head prev next front (Nil #lref) nx);
          unfold (add_rest1 head prev next front (Nil #lref) nx);
          rewrite (is_list_seg_s_with no_payload head nx next head 1.0R front)
               as (is_list_seg_s_with no_payload head nx next head 1.0R
                     (finit front @ [prev]));
          seg_s_peel_last no_payload head nx next head (finit front) prev;
          with vp. assert (R.pts_to prev #1.0R vp);
          rewrite (R.pts_to next #1.0R vn) as (R.pts_to head #1.0R vn);
          rewrite (is_list_seg_s_with no_payload head nx prev head 1.0R (finit front))
               as (is_list_seg_s_with no_payload head (lnext vn) prev head 1.0R
                     (finit (f0 :: ft)));
          fold (add_rest2 head prev next (f0 :: ft) (Nil #lref) nw nx (lprev vp));
          rewrite (add_rest2 head prev next (f0 :: ft) (Nil #lref) nw nx (lprev vp))
               as (add_rest2 head prev next front back nw nx (lprev vp));
        }
        Cons b0 bt -> {

          rewrite (add_rest1 head prev next front back nx)
               as (add_rest1 head prev next front (b0 :: bt) nx);
          unfold (add_rest1 head prev next front (b0 :: bt) nx);
          with hv. assert (R.pts_to head #1.0R hv);
          rewrite (is_list_seg_s_with no_payload head (lnext hv) next head 1.0R front)
               as (is_list_seg_s_with no_payload head (lnext hv) next head 1.0R
                     (finit front @ [prev]));
          seg_s_peel_last no_payload head (lnext hv) next head (finit front) prev;
          with vp. assert (R.pts_to prev #1.0R vp);
          rewrite (is_list_seg_s_with no_payload head (lnext hv) prev head 1.0R
                     (finit front))
               as (is_list_seg_s_with no_payload head (lnext hv) prev head 1.0R
                     (finit (f0 :: ft)));
          fold (add_rest2 head prev next (f0 :: ft) (b0 :: bt) nw nx (lprev vp));
          rewrite (add_rest2 head prev next (f0 :: ft) (b0 :: bt) nw nx (lprev vp))
               as (add_rest2 head prev next front back nw nx (lprev vp));
        }
      }
    }
  }
}

ghost
fn add_close (head prev next nw: lref) (front back: list lref) (#nx #pp: lref)
             (#vp: L.struct_list_node) (#vnw: L.struct_list_node)
  requires
    R.pts_to prev #1.0R vp **
    R.pts_to nw #1.0R vnw **
    add_rest2 head prev next front back nw nx pp **
    pure (lnext vp == nw) **
    pure (lprev vp == pp) **
    pure (vnw == mklink next prev)
  returns _: unit
  ensures is_list_ring head 1.0R (front @ (nw :: back))
{
  match front {
    Nil -> {
      match back {
        Nil -> {
          rewrite (add_rest2 head prev next front back nw nx pp)
               as (add_rest2 head prev next (Nil #lref) (Nil #lref) nw nx pp);
          unfold (add_rest2 head prev next (Nil #lref) (Nil #lref) nw nx pp);
          rewrite (R.pts_to prev #1.0R vp) as (R.pts_to head #1.0R vp);
          refs_distinct nw head;
          seg_nil_intro no_payload nw (lnext vnw) head 1.0R;
          seg_cons_intro no_payload head nw head 1.0R nw [];
          rewrite (is_list_seg_with no_payload head nw head 1.0R (nw :: []))
               as (is_list_seg_with no_payload head (lnext vp) head 1.0R
                     (front @ (nw :: back)));
          ring_close no_payload head;
        }
        Cons b0 bt -> {
          rewrite (add_rest2 head prev next front back nw nx pp)
               as (add_rest2 head prev next (Nil #lref) (b0 :: bt) nw nx pp);
          unfold (add_rest2 head prev next (Nil #lref) (b0 :: bt) nw nx pp);
          with vn. assert (R.pts_to next #1.0R vn);
          rewrite (R.pts_to prev #1.0R vp) as (R.pts_to head #1.0R vp);
          refs_distinct nw head;
          rewrite (is_list_seg_with no_payload next nx head 1.0R bt)
               as (is_list_seg_with no_payload next (lnext vn) head 1.0R bt);
          seg_cons_intro no_payload nw next head 1.0R b0 bt;
          rewrite (is_list_seg_with no_payload nw next head 1.0R (b0 :: bt))
               as (is_list_seg_with no_payload nw (lnext vnw) head 1.0R (b0 :: bt));
          seg_cons_intro no_payload head nw head 1.0R nw (b0 :: bt);
          last_or_append_cons head (Nil #lref) (b0 :: bt);
          last_or_append_cons head [nw] (b0 :: bt);
          rewrite (is_list_seg_with no_payload head nw head 1.0R (nw :: (b0 :: bt)))
               as (is_list_seg_with no_payload head (lnext vp) head 1.0R
                     (front @ (nw :: back)));
          ring_close no_payload head;
        }
      }
    }
    Cons f0 ft -> {
      last_or_flast head front;
      finit_flast_append front;
      match back {
        Nil -> {
          rewrite (add_rest2 head prev next front back nw nx pp)
               as (add_rest2 head prev next (f0 :: ft) (Nil #lref) nw nx pp);
          unfold (add_rest2 head prev next (f0 :: ft) (Nil #lref) nw nx pp);
          with vh. assert (R.pts_to head #1.0R vh);
          rewrite (is_list_seg_s_with no_payload head (lnext vh) prev head 1.0R
                     (finit (f0 :: ft)))
               as (is_list_seg_s_with no_payload head (lnext vh) prev head 1.0R
                     (finit front));

          rewrite (R.pts_to nw #1.0R vnw) as (R.pts_to (lnext vp) #1.0R vnw);
          seg_s_snoc no_payload head (lnext vh) head (finit front) prev;
          rewrite (R.pts_to (lnext vp) #1.0R vnw) as (R.pts_to nw #1.0R vnw);
          rewrite (is_list_seg_s_with no_payload head (lnext vh) (lnext vp) head 1.0R
                     (finit front @ [prev]))
               as (is_list_seg_s_with no_payload head (lnext vh) nw head 1.0R front);
          refs_distinct nw head;
          seg_nil_intro no_payload nw (lnext vnw) head 1.0R;
          seg_cons_intro no_payload prev nw head 1.0R nw [];
          rewrite (is_list_seg_with no_payload prev nw head 1.0R (nw :: []))
               as (is_list_seg_with no_payload (last_or head front) nw head 1.0R
                     (nw :: back));
          seg_merge no_payload head (lnext vh) nw head front (nw :: back);
          last_or_append_cons head front (nw :: back);
          ring_close no_payload head;
        }
        Cons b0 bt -> {
          rewrite (add_rest2 head prev next front back nw nx pp)
               as (add_rest2 head prev next (f0 :: ft) (b0 :: bt) nw nx pp);
          unfold (add_rest2 head prev next (f0 :: ft) (b0 :: bt) nw nx pp);
          with vh. assert (R.pts_to head #1.0R vh);
          with vn. assert (R.pts_to next #1.0R vn);
          rewrite (is_list_seg_s_with no_payload head (lnext vh) prev head 1.0R
                     (finit (f0 :: ft)))
               as (is_list_seg_s_with no_payload head (lnext vh) prev head 1.0R
                     (finit front));

          rewrite (R.pts_to nw #1.0R vnw) as (R.pts_to (lnext vp) #1.0R vnw);
          seg_s_snoc no_payload head (lnext vh) head (finit front) prev;
          rewrite (R.pts_to (lnext vp) #1.0R vnw) as (R.pts_to nw #1.0R vnw);
          rewrite (is_list_seg_s_with no_payload head (lnext vh) (lnext vp) head 1.0R
                     (finit front @ [prev]))
               as (is_list_seg_s_with no_payload head (lnext vh) nw head 1.0R front);
          rewrite (is_list_seg_with no_payload next nx head 1.0R bt)
               as (is_list_seg_with no_payload next (lnext vn) head 1.0R bt);
          seg_cons_intro no_payload nw next head 1.0R b0 bt;
          rewrite (is_list_seg_with no_payload nw next head 1.0R (b0 :: bt))
               as (is_list_seg_with no_payload nw (lnext vnw) head 1.0R (b0 :: bt));
          refs_distinct nw head;
          seg_cons_intro no_payload prev nw head 1.0R nw (b0 :: bt);
          rewrite (is_list_seg_with no_payload prev nw head 1.0R (nw :: (b0 :: bt)))
               as (is_list_seg_with no_payload (last_or head front) nw head 1.0R
                     (nw :: back));
          seg_merge no_payload head (lnext vh) nw head front (nw :: back);
          last_or_append_cons head front (b0 :: bt);
          last_or_append_cons head front (nw :: (b0 :: bt));
          last_or_append_cons head [nw] (b0 :: bt);
          ring_close no_payload head;
        }
      }
    }
  }
}

ghost
fn split_open_front_nil (pl: payload) (head: lref) (cells: list lref) (nxt: lref)
                        (#hv: L.struct_list_node)
  requires
    R.pts_to head #1.0R hv **
    is_list_seg_with pl head (lnext hv) head 1.0R cells **
    pure (lprev hv == last_or head cells) **
    pure (nxt == lnext hv)
  returns _: unit
  ensures is_list_split_with pl head 1.0R head nxt [] cells
{
  fold (is_list_seg_s_with pl head (lnext hv) nxt head 1.0R (Nil #lref));
  rewrite (is_list_seg_with pl head (lnext hv) head 1.0R cells)
       as (is_list_seg_with pl head nxt head 1.0R cells);
  fold (is_list_split_with pl head 1.0R head nxt [] cells);
}

ghost
fn split_open_back_nil (pl: payload) (head: lref) (cells: list lref) (pv: lref)
                       (#hv: L.struct_list_node)
  requires
    R.pts_to head #1.0R hv **
    is_list_seg_with pl head (lnext hv) head 1.0R cells **
    pure (lprev hv == last_or head cells) **
    pure (pv == lprev hv)
  returns _: unit
  ensures is_list_split_with pl head 1.0R pv head cells []
{
  FStar.List.Tot.Properties.append_l_nil cells;
  rewrite (is_list_seg_with pl head (lnext hv) head 1.0R cells)
       as (is_list_seg_with pl head (lnext hv) head 1.0R (cells @ []));
  seg_split pl head (lnext hv) head cells [];
  with mcur. assert (is_list_seg_with pl (last_or head cells) mcur head 1.0R []);
  unfold (is_list_seg_with pl (last_or head cells) mcur head 1.0R (Nil #lref));
  fold (is_list_seg_with pl pv head head 1.0R (Nil #lref));
  rewrite (is_list_seg_with pl pv head head 1.0R (Nil #lref))
       as (is_list_seg_with pl pv head head 1.0R ([] <: list lref));
  rewrite (is_list_seg_s_with pl head (lnext hv) mcur head 1.0R cells)
       as (is_list_seg_s_with pl head (lnext hv) head head 1.0R cells);
  fold (is_list_split_with pl head 1.0R pv head cells []);
}

let del_cut_with (pl: payload) (head prev next ent: lref) (front back: list lref) : slprop =
  exists* (hv: L.struct_list_node).
    R.pts_to head #1.0R hv **
    is_list_seg_s_with pl head (lnext hv) ent head 1.0R front **
    is_list_seg_with pl ent next head 1.0R back **
    pure (prev == last_or head front) **
    pure (ent =!= head) **
    pure (lprev hv == last_or head (front @ (ent :: back)))

unfold
let del_cut (head prev next ent: lref) (front back: list lref) : slprop =
  del_cut_with no_payload head prev next ent front back

ghost
fn del_cut_pl_out (pl: payload) (head prev next ent: lref) (front back: list lref)
  requires del_cut_with pl head prev next ent front back
  returns _: unit
  ensures del_cut_with no_payload head prev next ent front back
       ** payload_of pl (front @ back)
{
  unfold (del_cut_with pl head prev next ent front back);
  with hv. assert (R.pts_to head #1.0R hv);
  seg_s_pl_out pl head (lnext hv) ent head 1.0R front;
  seg_pl_out pl ent next head 1.0R back;
  payload_of_join pl front back;
  fold (del_cut_with no_payload head prev next ent front back);
}

ghost
fn del_cut_pl_in (pl: payload) (head prev next ent: lref) (front back: list lref)
  requires del_cut_with no_payload head prev next ent front back
        ** payload_of pl (front @ back)
  returns _: unit
  ensures del_cut_with pl head prev next ent front back
{
  unfold (del_cut_with no_payload head prev next ent front back);
  with hv. assert (R.pts_to head #1.0R hv);
  payload_of_split pl front back;
  seg_s_pl_in pl head (lnext hv) ent head 1.0R front;
  seg_pl_in pl ent next head 1.0R back;
  fold (del_cut_with pl head prev next ent front back);
}

let del_rest1 (head prev next ent: lref) (front back: list lref) (nx: lref) : slprop =
  match back with
  | [] ->
    is_list_seg_s head nx ent head 1.0R front **
    pure (next == head) **
    pure (prev == last_or head front) **
    pure (ent =!= head)
  | b0 :: bt ->
    exists* (hv: L.struct_list_node).
      R.pts_to head #1.0R hv **
      is_list_seg_s head (lnext hv) ent head 1.0R front **
      is_list_seg next nx head 1.0R bt **
      pure (next == b0) **
      pure (next =!= head) **
      pure (prev == last_or head front) **
      pure (ent =!= head) **
      pure (lprev hv == last_or head back)

ghost
fn del_expose_next (head prev next ent: lref) (front back: list lref)
  requires del_cut head prev next ent front back
  returns _: unit
  ensures
    exists* (vn: L.struct_list_node).
      R.pts_to next #1.0R vn **
      del_rest1 head prev next ent front back (lnext vn) **
      pure (lprev vn == ent)
{
  unfold (del_cut_with no_payload head prev next ent front back);
  with hv. assert (R.pts_to head #1.0R hv);
  match back {
    Nil -> {
      last_or_append_cons head front [ent];
      rewrite (is_list_seg_with no_payload ent next head 1.0R back)
           as (is_list_seg_with no_payload ent next head 1.0R (Nil #lref));
      seg_nil_elim no_payload ent next head 1.0R;
      rewrite (R.pts_to head #1.0R hv) as (R.pts_to next #1.0R hv);
      fold (del_rest1 head prev next ent front (Nil #lref) (lnext hv));
      rewrite (del_rest1 head prev next ent front (Nil #lref) (lnext hv))
           as (del_rest1 head prev next ent front back (lnext hv));
    }
    Cons b0 bt -> {
      rewrite (is_list_seg_with no_payload ent next head 1.0R back)
           as (is_list_seg_with no_payload ent next head 1.0R (b0 :: bt));
      seg_cons_elim no_payload ent next head 1.0R b0 bt;
      with vn. assert (R.pts_to next #1.0R vn);
      last_or_append_cons head front (ent :: (b0 :: bt));
      last_or_cons head ent (b0 :: bt);
      fold (del_rest1 head prev next ent front (b0 :: bt) (lnext vn));
      rewrite (del_rest1 head prev next ent front (b0 :: bt) (lnext vn))
           as (del_rest1 head prev next ent front back (lnext vn));
    }
  }
}

let del_rest2 (head prev next ent: lref) (front back: list lref) (nx pp: lref) : slprop =
  match front, back with
  | [], [] ->
    pure (prev == head /\ next == head /\ nx == ent /\ ent =!= head /\ pp == head)
  | [], b0 :: bt ->
    exists* (vn: L.struct_list_node).
      R.pts_to next #1.0R vn **
      is_list_seg next nx head 1.0R bt **
      pure (prev == head /\ next == b0 /\ next =!= head /\ ent =!= head) **
      pure (lprev vn == prev /\ lnext vn == nx) **
      pure (pp == last_or head back)
  | f0 :: ft, [] ->
    exists* (vh: L.struct_list_node).
      R.pts_to head #1.0R vh **
      is_list_seg_s head (lnext vh) prev head 1.0R (finit (f0 :: ft)) **
      pure (next == head /\ prev == flast (f0 :: ft) /\ prev =!= head /\ ent =!= head) **
      pure (lprev vh == prev /\ lnext vh == nx) **
      pure (pp == last_or head (finit (f0 :: ft)))
  | f0 :: ft, b0 :: bt ->
    exists* (vh: L.struct_list_node) (vn: L.struct_list_node).
      R.pts_to head #1.0R vh **
      R.pts_to next #1.0R vn **
      is_list_seg_s head (lnext vh) prev head 1.0R (finit (f0 :: ft)) **
      is_list_seg next nx head 1.0R bt **
      pure (prev == flast (f0 :: ft) /\ prev =!= head /\ ent =!= head) **
      pure (next == b0 /\ next =!= head) **
      pure (lprev vn == prev /\ lnext vn == nx) **
      pure (lprev vh == last_or head back) **
      pure (pp == last_or head (finit (f0 :: ft)))

ghost
fn del_reseat (head prev next ent: lref) (front back: list lref) (#nx: lref)
              (#vn: L.struct_list_node)
  requires
    R.pts_to next #1.0R vn **
    del_rest1 head prev next ent front back nx **
    pure (lprev vn == prev) **
    pure (lnext vn == nx)
  returns _: unit
  ensures
    exists* (vp: L.struct_list_node).
      R.pts_to prev #1.0R vp **
      del_rest2 head prev next ent front back nx (lprev vp) **
      pure (lnext vp == ent)
{
  match front {
    Nil -> {
      match back {
        Nil -> {

          rewrite (del_rest1 head prev next ent front back nx)
               as (del_rest1 head prev next ent (Nil #lref) (Nil #lref) nx);
          unfold (del_rest1 head prev next ent (Nil #lref) (Nil #lref) nx);
          unfold (is_list_seg_s_with no_payload head nx ent head 1.0R (Nil #lref));
          rewrite (R.pts_to next #1.0R vn) as (R.pts_to prev #1.0R vn);
          fold (del_rest2 head prev next ent (Nil #lref) (Nil #lref) nx (lprev vn));
          rewrite (del_rest2 head prev next ent (Nil #lref) (Nil #lref) nx (lprev vn))
               as (del_rest2 head prev next ent front back nx (lprev vn));
        }
        Cons b0 bt -> {

          rewrite (del_rest1 head prev next ent front back nx)
               as (del_rest1 head prev next ent (Nil #lref) (b0 :: bt) nx);
          unfold (del_rest1 head prev next ent (Nil #lref) (b0 :: bt) nx);
          with hv. assert (R.pts_to head #1.0R hv);
          unfold (is_list_seg_s_with no_payload head (lnext hv) ent head 1.0R (Nil #lref));
          rewrite (R.pts_to head #1.0R hv) as (R.pts_to prev #1.0R hv);
          fold (del_rest2 head prev next ent (Nil #lref) (b0 :: bt) nx (lprev hv));
          rewrite (del_rest2 head prev next ent (Nil #lref) (b0 :: bt) nx (lprev hv))
               as (del_rest2 head prev next ent front back nx (lprev hv));
        }
      }
    }
    Cons f0 ft -> {
      last_or_flast head front;
      finit_flast_append front;
      match back {
        Nil -> {

          rewrite (del_rest1 head prev next ent front back nx)
               as (del_rest1 head prev next ent (f0 :: ft) (Nil #lref) nx);
          unfold (del_rest1 head prev next ent (f0 :: ft) (Nil #lref) nx);
          rewrite (R.pts_to next #1.0R vn) as (R.pts_to head #1.0R vn);
          rewrite (is_list_seg_s_with no_payload head nx ent head 1.0R (f0 :: ft))
               as (is_list_seg_s_with no_payload head nx ent head 1.0R
                     (finit (f0 :: ft) @ [flast (f0 :: ft)]));
          seg_s_peel_last no_payload head nx ent head
                          (finit (f0 :: ft)) (flast (f0 :: ft));
          with vl. assert (R.pts_to (flast (f0 :: ft)) #1.0R vl);
          rewrite (R.pts_to (flast (f0 :: ft)) #1.0R vl) as (R.pts_to prev #1.0R vl);
          rewrite (is_list_seg_s_with no_payload head nx (flast (f0 :: ft)) head 1.0R
                     (finit (f0 :: ft)))
               as (is_list_seg_s_with no_payload head (lnext vn) prev head 1.0R
                     (finit (f0 :: ft)));
          refs_distinct prev head;
          fold (del_rest2 head prev next ent (f0 :: ft) (Nil #lref) nx (lprev vl));
          rewrite (del_rest2 head prev next ent (f0 :: ft) (Nil #lref) nx (lprev vl))
               as (del_rest2 head prev next ent front back nx (lprev vl));
        }
        Cons b0 bt -> {
          rewrite (del_rest1 head prev next ent front back nx)
               as (del_rest1 head prev next ent (f0 :: ft) (b0 :: bt) nx);
          unfold (del_rest1 head prev next ent (f0 :: ft) (b0 :: bt) nx);
          with hv. assert (R.pts_to head #1.0R hv);
          rewrite (is_list_seg_s_with no_payload head (lnext hv) ent head 1.0R (f0 :: ft))
               as (is_list_seg_s_with no_payload head (lnext hv) ent head 1.0R
                     (finit (f0 :: ft) @ [flast (f0 :: ft)]));
          seg_s_peel_last no_payload head (lnext hv) ent head
                          (finit (f0 :: ft)) (flast (f0 :: ft));
          with vl. assert (R.pts_to (flast (f0 :: ft)) #1.0R vl);
          rewrite (R.pts_to (flast (f0 :: ft)) #1.0R vl) as (R.pts_to prev #1.0R vl);
          rewrite (is_list_seg_s_with no_payload head (lnext hv) (flast (f0 :: ft)) head
                     1.0R (finit (f0 :: ft)))
               as (is_list_seg_s_with no_payload head (lnext hv) prev head 1.0R
                     (finit (f0 :: ft)));
          refs_distinct prev head;
          fold (del_rest2 head prev next ent (f0 :: ft) (b0 :: bt) nx (lprev vl));
          rewrite (del_rest2 head prev next ent (f0 :: ft) (b0 :: bt) nx (lprev vl))
               as (del_rest2 head prev next ent front back nx (lprev vl));
        }
      }
    }
  }
}

ghost
fn del_close (head prev next ent: lref) (front back: list lref) (#nx #pp: lref)
             (#vp: L.struct_list_node)
  requires
    R.pts_to prev #1.0R vp **
    del_rest2 head prev next ent front back nx pp **
    pure (lnext vp == next) **
    pure (lprev vp == pp)
  returns _: unit
  ensures is_list_ring head 1.0R (front @ back)
{
  match front {
    Nil -> {
      match back {
        Nil -> {
          rewrite (del_rest2 head prev next ent front back nx pp)
               as (del_rest2 head prev next ent (Nil #lref) (Nil #lref) nx pp);
          unfold (del_rest2 head prev next ent (Nil #lref) (Nil #lref) nx pp);
          rewrite (R.pts_to prev #1.0R vp) as (R.pts_to head #1.0R vp);
          seg_nil_intro no_payload head (lnext vp) head 1.0R;
          rewrite (is_list_seg_with no_payload head (lnext vp) head 1.0R [])
               as (is_list_seg_with no_payload head (lnext vp) head 1.0R (front @ back));
          ring_close no_payload head;
        }
        Cons b0 bt -> {
          rewrite (del_rest2 head prev next ent front back nx pp)
               as (del_rest2 head prev next ent (Nil #lref) (b0 :: bt) nx pp);
          unfold (del_rest2 head prev next ent (Nil #lref) (b0 :: bt) nx pp);
          with vn. assert (R.pts_to next #1.0R vn);
          rewrite (R.pts_to prev #1.0R vp) as (R.pts_to head #1.0R vp);
          rewrite (is_list_seg_with no_payload next nx head 1.0R bt)
               as (is_list_seg_with no_payload next (lnext vn) head 1.0R bt);
          seg_cons_intro no_payload head next head 1.0R b0 bt;
          rewrite (is_list_seg_with no_payload head next head 1.0R (b0 :: bt))
               as (is_list_seg_with no_payload head (lnext vp) head 1.0R (front @ back));
          ring_close no_payload head;
        }
      }
    }
    Cons f0 ft -> {
      last_or_flast head front;
      finit_flast_append front;
      match back {
        Nil -> {
          rewrite (del_rest2 head prev next ent front back nx pp)
               as (del_rest2 head prev next ent (f0 :: ft) (Nil #lref) nx pp);
          unfold (del_rest2 head prev next ent (f0 :: ft) (Nil #lref) nx pp);
          with vh. assert (R.pts_to head #1.0R vh);
          rewrite (is_list_seg_s_with no_payload head (lnext vh) prev head 1.0R
                     (finit (f0 :: ft)))
               as (is_list_seg_s_with no_payload head (lnext vh) prev head 1.0R
                     (finit front));

          rewrite (R.pts_to head #1.0R vh) as (R.pts_to (lnext vp) #1.0R vh);
          seg_s_snoc no_payload head (lnext vh) head (finit front) prev;
          rewrite (R.pts_to (lnext vp) #1.0R vh) as (R.pts_to head #1.0R vh);
          rewrite (is_list_seg_s_with no_payload head (lnext vh) (lnext vp) head 1.0R
                     (finit front @ [prev]))
               as (is_list_seg_s_with no_payload head (lnext vh) head head 1.0R front);
          seg_nil_intro no_payload (last_or head front) head head 1.0R;
          rewrite (is_list_seg_with no_payload (last_or head front) head head 1.0R [])
               as (is_list_seg_with no_payload (last_or head front) head head 1.0R back);
          seg_merge no_payload head (lnext vh) head head front back;
          FStar.List.Tot.Properties.append_l_nil front;
          ring_close no_payload head;
        }
        Cons b0 bt -> {
          rewrite (del_rest2 head prev next ent front back nx pp)
               as (del_rest2 head prev next ent (f0 :: ft) (b0 :: bt) nx pp);
          unfold (del_rest2 head prev next ent (f0 :: ft) (b0 :: bt) nx pp);
          with vh. assert (R.pts_to head #1.0R vh);
          with vn. assert (R.pts_to next #1.0R vn);
          rewrite (is_list_seg_s_with no_payload head (lnext vh) prev head 1.0R
                     (finit (f0 :: ft)))
               as (is_list_seg_s_with no_payload head (lnext vh) prev head 1.0R
                     (finit front));
          rewrite (R.pts_to next #1.0R vn) as (R.pts_to (lnext vp) #1.0R vn);
          seg_s_snoc no_payload head (lnext vh) head (finit front) prev;
          rewrite (R.pts_to (lnext vp) #1.0R vn) as (R.pts_to next #1.0R vn);
          rewrite (is_list_seg_s_with no_payload head (lnext vh) (lnext vp) head 1.0R
                     (finit front @ [prev]))
               as (is_list_seg_s_with no_payload head (lnext vh) next head 1.0R front);
          rewrite (is_list_seg_with no_payload next nx head 1.0R bt)
               as (is_list_seg_with no_payload next (lnext vn) head 1.0R bt);
          seg_cons_intro no_payload prev next head 1.0R b0 bt;
          rewrite (is_list_seg_with no_payload prev next head 1.0R (b0 :: bt))
               as (is_list_seg_with no_payload (last_or head front) next head 1.0R back);
          seg_merge no_payload head (lnext vh) next head front back;
          last_or_append_cons head front back;
          ring_close no_payload head;
        }
      }
    }
  }
}

ghost
fn del_open (head ent: lref) (front back: list lref)
  requires is_list_ring head 1.0R (front @ (ent :: back))
  returns _: unit
  ensures
    exists* (ev: L.struct_list_node).
      R.pts_to ent #1.0R ev **
      del_cut head (lprev ev) (lnext ev) ent front back
{
  ring_open no_payload head;
  with hv. assert (R.pts_to head #1.0R hv);
  seg_split no_payload head (lnext hv) head front (ent :: back);
  with mcur. assert (is_list_seg_with no_payload (last_or head front) mcur head 1.0R
                       (ent :: back));
  seg_cons_elim no_payload (last_or head front) mcur head 1.0R ent back;
  with ev. assert (R.pts_to mcur #1.0R ev);
  rewrite (R.pts_to mcur #1.0R ev) as (R.pts_to ent #1.0R ev);
  rewrite (is_list_seg_with no_payload mcur (lnext ev) head 1.0R back)
       as (is_list_seg_with no_payload ent (lnext ev) head 1.0R back);
  rewrite (is_list_seg_s_with no_payload head (lnext hv) mcur head 1.0R front)
       as (is_list_seg_s_with no_payload head (lnext hv) ent head 1.0R front);
  fold (del_cut_with no_payload head (lprev ev) (lnext ev) ent front back);
}

ghost
fn del_cut_pin (head prev next ent: lref) (front back: list lref) (#pv #nx: lref)
  requires
    del_cut head pv nx ent front back **
    pure (prev == pv) **
    pure (next == nx)
  returns _: unit
  ensures del_cut head prev next ent front back
{
  rewrite (del_cut head pv nx ent front back)
       as (del_cut head prev next ent front back);
}

let iter_inv_g (pl: payload) (head pos: lref) (n: int) (cells: list lref) : slprop =
  exists* (front back: list lref).
    is_list_split_with pl head 1.0R (last_or head front) pos front back **
    pure (front @ back == cells) **
    pure (n == length front) **
    pure (length front + length back == length cells)

let iter_mid_g (pl: payload) (head pos: lref) (nfront: int) (cells: list lref)
               (v: L.struct_list_node) : slprop =
  exists* (front: list lref) (b0: lref) (bt: list lref).
    iter_rest pl head (last_or head front) pos front b0 bt (lnext v) **
    pure (front @ (b0 :: bt) == cells) **
    pure (length front == nfront) **
    pure (lprev v == last_or head front) **
    pure (pos == b0)

ghost
fn iter_inv_intro_g (pl: payload) (head pos: lref) (#cells: list lref)
  requires is_list_split_with pl head 1.0R head pos [] cells
  ensures  iter_inv_g pl head pos 0 cells ** pure (0 <= length cells)
{

  rewrite (is_list_split_with pl head 1.0R head pos [] cells)
       as (is_list_split_with pl head 1.0R (last_or head []) pos [] cells);
  fold (iter_inv_g pl head pos 0 cells);
}

ghost
fn iter_inv_intro_at_g (pl: payload) (head pos: lref) (front back: list lref)
  requires is_list_split_with pl head 1.0R (last_or head front) pos front back
  ensures  iter_inv_g pl head pos (length front) (front @ back) **
           pure (length front <= length (front @ back))
{
  FStar.List.Tot.Properties.append_length front back;
  fold (iter_inv_g pl head pos (length front) (front @ back));
}

ghost
fn iter_open_g (pl: payload) (head: lref) (cells: list lref)
               (#pos: lref) (#n: int)
  requires iter_inv_g pl head pos n cells ** pure (pos =!= head)
  returns _: unit
  ensures
    exists* (v: L.struct_list_node).
      R.pts_to pos v ** pl pos **
      iter_mid_g pl head pos n cells v **
      pure (n < length cells)
{
  unfold (iter_inv_g pl head pos n cells);
  with front back.
    assert (is_list_split_with pl head 1.0R (last_or head front) pos front back);
  split_cur_ne pl head (last_or head front) pos front back;
  let b0 = Cons?.hd back;
  let bt = Cons?.tl back;
  rewrite (is_list_split_with pl head 1.0R (last_or head front) pos front back)
       as (is_list_split_with pl head 1.0R (last_or head front) pos front (b0 :: bt));
  iter_expose pl head (last_or head front) pos front b0 bt;
  with v. assert (R.pts_to pos v);
  fold (iter_mid_g pl head pos n cells v);
}

ghost
fn iter_step_g (pl: payload) (head: lref) (n': int) (cells: list lref)
               (#pos: lref) (#nfront: int) (#v: L.struct_list_node)
  requires
    R.pts_to pos v ** pl pos **
    iter_mid_g pl head pos nfront cells v **
    pure (n' == nfront + 1)
  returns _: unit
  ensures iter_inv_g pl head (lnext v) n' cells **
          pure (n' <= length cells)
{
  unfold (iter_mid_g pl head pos nfront cells v);
  with front b0 bt.
    assert (iter_rest pl head (last_or head front) pos front b0 bt (lnext v));
  iter_advance pl head (last_or head front) pos front b0 bt;
  last_or_snoc head front pos;
  FStar.List.Tot.Properties.append_assoc front [pos] bt;
  FStar.List.Tot.Properties.append_length front [pos];
  FStar.List.Tot.Properties.append_length (front @ [pos]) bt;
  rewrite (is_list_split_with pl head 1.0R pos (lnext v) (front @ [pos]) bt)
       as (is_list_split_with pl head 1.0R
             (last_or head (front @ [pos])) (lnext v) (front @ [pos]) bt);
  fold (iter_inv_g pl head (lnext v) n' cells);
}

ghost
fn iter_finish_g (pl: payload) (head: lref) (cells: list lref)
                 (#pos: lref) (#n: int)
  requires iter_inv_g pl head pos n cells ** pure (pos == head)
  returns _: unit
  ensures is_list_ring_with pl head 1.0R cells **
          pure (n == length cells)
{
  unfold (iter_inv_g pl head pos n cells);
  with front back.
    assert (is_list_split_with pl head 1.0R (last_or head front) pos front back);
  split_cur_ne pl head (last_or head front) pos front back;
  split_close pl head (last_or head front) pos front back;
  FStar.List.Tot.Properties.append_l_nil front;
  rewrite (is_list_ring_with pl head 1.0R (front @ back))
       as (is_list_ring_with pl head 1.0R cells);
}

let iter_cur_rest_at_g (pl: payload) (head pos: lref)
                       (v: L.struct_list_node) (front back: list lref) : slprop =
  match back with
  | [] ->
    is_list_seg_s_with pl head (lnext v) pos head 1.0R front **
    is_list_seg_with pl (last_or head front) pos head 1.0R [] **
    pure (pos == head) **
    pure (lprev v == last_or head front)
  | b0 :: bt ->
    pl pos **
    iter_rest pl head (last_or head front) pos front b0 bt (lnext v) **
    pure (pos =!= head) **
    pure (pos == b0) **
    pure (lprev v == last_or head front)

let iter_cur_inv_g (pl: payload) (head pos: lref) (n: int) (cells: list lref)
                   (v: L.struct_list_node) : slprop =
  exists* (front back: list lref).
    iter_cur_rest_at_g pl head pos v front back **
    pure (front @ back == cells) **
    pure (n == length front) **
    pure (length front + length back == length cells)

ghost
fn iter_cur_expose_at_g (pl: payload) (head pos: lref) (front back: list lref)
  requires
    is_list_split_with pl head 1.0R (last_or head front) pos front back **
    pure ((pos == head) <==> (back == []))
  returns _: unit
  ensures
    exists* (v: L.struct_list_node).
      R.pts_to pos #1.0R v ** iter_cur_rest_at_g pl head pos v front back
{
  match back {
    Nil -> {
      rewrite (is_list_split_with pl head 1.0R (last_or head front) pos front back)
           as (is_list_split_with pl head 1.0R (last_or head front) pos front (Nil #lref));
      unfold (is_list_split_with pl head 1.0R (last_or head front) pos front (Nil #lref));
      with hv. assert (R.pts_to head #1.0R hv);
      FStar.List.Tot.Properties.append_l_nil front;
      rewrite (R.pts_to head #1.0R hv) as (R.pts_to pos #1.0R hv);
      rewrite (is_list_seg_s_with pl head (lnext hv) pos head 1.0R front)
           as (is_list_seg_s_with pl head (lnext hv) pos head 1.0R front);
      fold (iter_cur_rest_at_g pl head pos hv front (Nil #lref));
      rewrite (iter_cur_rest_at_g pl head pos hv front (Nil #lref))
           as (iter_cur_rest_at_g pl head pos hv front back);
    }
    Cons b0 bt -> {
      rewrite (is_list_split_with pl head 1.0R (last_or head front) pos front back)
           as (is_list_split_with pl head 1.0R (last_or head front) pos front (b0 :: bt));
      iter_expose pl head (last_or head front) pos front b0 bt;
      with vn. assert (R.pts_to pos #1.0R vn);
      fold (iter_cur_rest_at_g pl head pos vn front (b0 :: bt));
      rewrite (iter_cur_rest_at_g pl head pos vn front (b0 :: bt))
           as (iter_cur_rest_at_g pl head pos vn front back);
    }
  }
}

ghost
fn iter_cur_expose_g (pl: payload) (head: lref) (cells: list lref)
                     (#pos: lref) (#n: int)
  requires iter_inv_g pl head pos n cells
  returns _: unit
  ensures
    exists* (v: L.struct_list_node).
      R.pts_to pos #1.0R v ** iter_cur_inv_g pl head pos n cells v
{
  unfold (iter_inv_g pl head pos n cells);
  with front back.
    assert (is_list_split_with pl head 1.0R (last_or head front) pos front back);
  split_cur_ne pl head (last_or head front) pos front back;
  iter_cur_expose_at_g pl head pos front back;
  with v. assert (R.pts_to pos #1.0R v);
  fold (iter_cur_inv_g pl head pos n cells v);
}

ghost
fn iter_cur_to_mid_at_g (pl: payload) (head pos: lref) (n: int) (cells: list lref)
                        (front back: list lref) (#v: L.struct_list_node)
  requires
    R.pts_to pos #1.0R v **
    iter_cur_rest_at_g pl head pos v front back **
    pure (pos =!= head) ** pure (front @ back == cells) ** pure (n == length front)
  returns _: unit
  ensures
    R.pts_to pos #1.0R v ** pl pos **
    iter_mid_g pl head pos n cells v **
    pure (n < length cells)
{
  match back {
    Nil -> {
      rewrite (iter_cur_rest_at_g pl head pos v front back)
           as (iter_cur_rest_at_g pl head pos v front (Nil #lref));
      unfold (iter_cur_rest_at_g pl head pos v front (Nil #lref));
      unreachable ()
    }
    Cons b0 bt -> {
      rewrite (iter_cur_rest_at_g pl head pos v front back)
           as (iter_cur_rest_at_g pl head pos v front (b0 :: bt));
      unfold (iter_cur_rest_at_g pl head pos v front (b0 :: bt));
      FStar.List.Tot.Properties.append_length front back;
      fold (iter_mid_g pl head pos n cells v);
    }
  }
}

ghost
fn iter_cur_to_mid_g (pl: payload) (head: lref) (cells: list lref)
                     (#pos: lref) (#n: int) (#v: L.struct_list_node)
  requires
    R.pts_to pos #1.0R v ** iter_cur_inv_g pl head pos n cells v **
    pure (pos =!= head)
  returns _: unit
  ensures
    R.pts_to pos #1.0R v ** pl pos **
    iter_mid_g pl head pos n cells v **
    pure (n < length cells)
{
  unfold (iter_cur_inv_g pl head pos n cells v);
  with front back. assert (iter_cur_rest_at_g pl head pos v front back);
  iter_cur_to_mid_at_g pl head pos n cells front back;
}

ghost
fn iter_cur_finish_at_g (pl: payload) (head pos: lref) (n: int) (cells: list lref)
                        (front back: list lref) (#v: L.struct_list_node)
  requires
    R.pts_to pos #1.0R v **
    iter_cur_rest_at_g pl head pos v front back **
    pure (pos == head) ** pure (front @ back == cells) ** pure (n == length front)
  returns _: unit
  ensures is_list_ring_with pl head 1.0R cells ** pure (n == length cells)
{
  match back {
    Nil -> {
      rewrite (iter_cur_rest_at_g pl head pos v front back)
           as (iter_cur_rest_at_g pl head pos v front (Nil #lref));
      unfold (iter_cur_rest_at_g pl head pos v front (Nil #lref));
      FStar.List.Tot.Properties.append_l_nil front;
      rewrite (R.pts_to pos #1.0R v) as (R.pts_to head #1.0R v);
      rewrite (is_list_seg_s_with pl head (lnext v) pos head 1.0R front)
           as (is_list_seg_s_with pl head (lnext v) head head 1.0R front);
      rewrite (is_list_seg_with pl (last_or head front) pos head 1.0R (Nil #lref))
           as (is_list_seg_with pl (last_or head front) head head 1.0R (Nil #lref));
      fold (is_list_split_with pl head 1.0R (last_or head front) head front (Nil #lref));
      split_close pl head (last_or head front) head front (Nil #lref);
      rewrite (is_list_ring_with pl head 1.0R (front @ (Nil #lref)))
           as (is_list_ring_with pl head 1.0R cells);
    }
    Cons b0 bt -> {
      rewrite (iter_cur_rest_at_g pl head pos v front back)
           as (iter_cur_rest_at_g pl head pos v front (b0 :: bt));
      unfold (iter_cur_rest_at_g pl head pos v front (b0 :: bt));
      unreachable ()
    }
  }
}

ghost
fn iter_cur_finish_g (pl: payload) (head: lref) (cells: list lref)
                     (#pos: lref) (#n: int) (#v: L.struct_list_node)
  requires
    R.pts_to pos #1.0R v ** iter_cur_inv_g pl head pos n cells v **
    pure (pos == head)
  returns _: unit
  ensures is_list_ring_with pl head 1.0R cells ** pure (n == length cells)
{
  unfold (iter_cur_inv_g pl head pos n cells v);
  with front back. assert (iter_cur_rest_at_g pl head pos v front back);
  iter_cur_finish_at_g pl head pos n cells front back;
}

ghost
fn iter_cur_step_g (pl: payload) (head: lref) (n': int) (cells: list lref)
                   (#pos: lref) (#n: int) (#v: L.struct_list_node)
  requires
    R.pts_to pos #1.0R v ** iter_cur_inv_g pl head pos n cells v **
    pure (pos =!= head) ** pure (n' == n + 1)
  returns _: unit
  ensures
    exists* (v': L.struct_list_node).
      R.pts_to (lnext v) #1.0R v' **
      iter_cur_inv_g pl head (lnext v) n' cells v' **
      pure (n' <= length cells)
{
  iter_cur_to_mid_g pl head cells;
  iter_step_g pl head n' cells;
  iter_cur_expose_g pl head cells;
}

let safe_inv_g (pl: payload) (head pos: lref) (n: int) (cells: list lref)
               (nx: lref) : slprop =
  exists* (v: L.struct_list_node).
    R.pts_to pos #1.0R v **
    iter_cur_inv_g pl head pos n cells v **
    pure (nx == lnext v)

ghost
fn safe_open_g (pl: payload) (head pos: lref) (cells: list lref)
               (nx: lref) (#n: int)
  requires safe_inv_g pl head pos n cells nx
  returns _: unit
  ensures
    exists* (v: L.struct_list_node).
      R.pts_to pos #1.0R v **
      iter_cur_inv_g pl head pos n cells v **
      pure (nx == lnext v)
{
  unfold (safe_inv_g pl head pos n cells nx);
}

ghost
fn safe_close_g (pl: payload) (head pos: lref) (cells: list lref)
                (nx: lref) (#n: int) (#v: L.struct_list_node)
  requires
    R.pts_to pos #1.0R v **
    iter_cur_inv_g pl head pos n cells v **
    pure (nx == lnext v)
  returns _: unit
  ensures safe_inv_g pl head pos n cells nx
{
  fold (safe_inv_g pl head pos n cells nx);
}

ghost
fn safe_step_g (pl: payload) (head pos nx: lref) (n': int) (cells: list lref)
               (#n: int)
  requires
    safe_inv_g pl head pos n cells nx **
    pure (pos =!= head) ** pure (n' == n + 1)
  returns _: unit
  ensures
    exists* (v': L.struct_list_node).
      R.pts_to nx #1.0R v' **
      iter_cur_inv_g pl head nx n' cells v' **
      pure (n' <= length cells)
{
  unfold (safe_inv_g pl head pos n cells nx);
  with v. assert (R.pts_to pos #1.0R v);
  iter_cur_to_mid_g pl head cells;
  iter_step_g pl head n' cells;
  rewrite (iter_inv_g pl head (lnext v) n' cells)
       as (iter_inv_g pl head nx n' cells);
  iter_cur_expose_g pl head cells;
}

ghost
fn iter_close_g (pl: payload) (head: lref) (cells: list lref)
                (#pos: lref) (#n: int) (#v: L.struct_list_node)
  requires
    R.pts_to pos v ** pl pos ** iter_mid_g pl head pos n cells v
  returns _: unit
  ensures iter_inv_g pl head pos n cells
{
  unfold (iter_mid_g pl head pos n cells v);
  with front b0 bt.
    assert (iter_rest pl head (last_or head front) pos front b0 bt (lnext v));
  iter_unexpose pl head (last_or head front) pos front b0 bt;
  FStar.List.Tot.Properties.append_length front (b0 :: bt);
  fold (iter_inv_g pl head pos n cells);
}

ghost
fn iter_mid_to_cur_g (pl: payload) (head: lref) (cells: list lref)
                     (#pos: lref) (#n: int) (#v: L.struct_list_node)
  requires
    R.pts_to pos #1.0R v ** pl pos **
    iter_mid_g pl head pos n cells v ** pure (pos =!= head)
  returns _: unit
  ensures
    R.pts_to pos #1.0R v ** iter_cur_inv_g pl head pos n cells v
{
  unfold (iter_mid_g pl head pos n cells v);
  with front b0 bt.
    assert (iter_rest pl head (last_or head front) pos front b0 bt (lnext v));
  FStar.List.Tot.Properties.append_length front (b0 :: bt);
  fold (iter_cur_rest_at_g pl head pos v front (b0 :: bt));
  fold (iter_cur_inv_g pl head pos n cells v);
}

(* An additional index records each member's resource without indexing its links. *)
let ipayload (a: Type0) = lref -> a -> slprop

let rec cells_of (#a: Type0) (es: list (lref & a))
  : Tot (list lref) (decreases es)
  = match es with
    | [] -> []
    | x :: tl -> fst x :: cells_of tl

let cells_of_nil (#a: Type0) ()
  : Lemma (cells_of #a [] == []) = ()

let cells_of_nil_iff (#a: Type0) (es: list (lref & a))
  : Lemma (ensures Nil? (cells_of es) <==> Nil? es)
          [SMTPat (cells_of es)]
  = match es with | [] -> () | _ :: _ -> ()

let rec cells_of_append (#a: Type0) (u v: list (lref & a))
  : Lemma (ensures cells_of (u @ v) == cells_of u @ cells_of v)
          (decreases u)
          [SMTPat (cells_of (u @ v))]
  = match u with
    | [] -> ()
    | _ :: tl -> cells_of_append tl v

let rec cells_of_split (#a: Type0) (front back: list (lref & a)) (c: lref) (x: a)
  : Lemma (ensures cells_of (front @ ((c, x) :: back))
                == cells_of front @ (c :: cells_of back))
          (decreases front)
  = match front with
    | [] -> ()
    | _ :: tl -> cells_of_split tl back c x

let rec ipayload_of (#a: Type0) (ipl: ipayload a) (es: list (lref & a))
  : Tot slprop (decreases es)
  = match es with
    | [] -> emp
    | x :: tl -> ipl (fst x) (snd x) ** ipayload_of ipl tl

let is_list_seg_ix
    (#a: Type0) (ipl: ipayload a) (prev cur endl: lref) (p: perm)
    (es: list (lref & a))
  : slprop
  = is_list_seg prev cur endl p (cells_of es) ** ipayload_of ipl es

let is_list_ring_ix
    (#a: Type0) (ipl: ipayload a) ([@@@mkey] head: lref) (p: perm)
    (es: list (lref & a))
  : slprop
  = is_list_ring head p (cells_of es) ** ipayload_of ipl es

ghost
fn ring_ix_out (#a: Type0) (ipl: ipayload a) (head: lref) (p: perm) (es: list (lref & a))
  requires is_list_ring_ix ipl head p es
  returns _: unit
  ensures is_list_ring head p (cells_of es) ** ipayload_of ipl es
{
  unfold (is_list_ring_ix ipl head p es);
}

ghost
fn ring_ix_in (#a: Type0) (ipl: ipayload a) (head: lref) (p: perm) (es: list (lref & a))
  requires is_list_ring head p (cells_of es) ** ipayload_of ipl es
  returns _: unit
  ensures is_list_ring_ix ipl head p es
{
  fold (is_list_ring_ix ipl head p es);
}

ghost
fn seg_ix_out (#a: Type0) (ipl: ipayload a) (prev cur endl: lref) (p: perm)
              (es: list (lref & a))
  requires is_list_seg_ix ipl prev cur endl p es
  returns _: unit
  ensures is_list_seg prev cur endl p (cells_of es) ** ipayload_of ipl es
{
  unfold (is_list_seg_ix ipl prev cur endl p es);
}

ghost
fn seg_ix_in (#a: Type0) (ipl: ipayload a) (prev cur endl: lref) (p: perm)
             (es: list (lref & a))
  requires is_list_seg prev cur endl p (cells_of es) ** ipayload_of ipl es
  returns _: unit
  ensures is_list_seg_ix ipl prev cur endl p es
{
  fold (is_list_seg_ix ipl prev cur endl p es);
}

let emp_pl : payload = no_payload

ghost
fn epl_in (head: lref) (p: perm) (cs: list lref)
  requires is_list_ring head p cs
  returns _: unit
  ensures is_list_ring_with emp_pl head p cs
{
  rewrite (is_list_ring head p cs) as (is_list_ring_with emp_pl head p cs);
}

ghost
fn epl_out (head: lref) (p: perm) (cs: list lref)
  requires is_list_ring_with emp_pl head p cs
  returns _: unit
  ensures is_list_ring head p cs
{
  rewrite (is_list_ring_with emp_pl head p cs) as (is_list_ring head p cs);
}

ghost
fn epl_single_in (c: lref)
  requires emp
  returns _: unit
  ensures payload_of emp_pl [c]
{
  rewrite emp as (emp_pl c);
  payload_of_single_in emp_pl c;
}

ghost
fn epl_single_out (c: lref)
  requires payload_of emp_pl [c]
  returns _: unit
  ensures emp
{
  payload_of_single_out emp_pl c;
  rewrite (emp_pl c) as emp;
}

ghost
fn ring_ix_open (#a: Type0) (ipl: ipayload a) (head: lref) (p: perm)
                (es: list (lref & a))
  requires is_list_ring_ix ipl head p es
  returns _: unit
  ensures is_list_ring_with emp_pl head p (cells_of es) ** ipayload_of ipl es
{
  ring_ix_out ipl head p es;
  epl_in head p (cells_of es);
}

ghost
fn ring_ix_close (#a: Type0) (ipl: ipayload a) (head: lref) (p: perm)
                 (es: list (lref & a))
  requires is_list_ring_with emp_pl head p (cells_of es) ** ipayload_of ipl es
  returns _: unit
  ensures is_list_ring_ix ipl head p es
{
  epl_out head p (cells_of es);
  ring_ix_in ipl head p es;
}

ghost
fn ring_ix_open_at (#a: Type0) (ipl: ipayload a) (head: lref) (p: perm)
                   (front back: list (lref & a)) (c: lref) (x: a)
  requires is_list_ring_ix ipl head p (front @ ((c, x) :: back))
  returns _: unit
  ensures is_list_ring_with emp_pl head p (cells_of front @ (c :: cells_of back))
       ** ipayload_of ipl (front @ ((c, x) :: back))
{
  ring_ix_out ipl head p (front @ ((c, x) :: back));
  cells_of_split front back c x;
  rewrite (is_list_ring head p (cells_of (front @ ((c, x) :: back))))
       as (is_list_ring head p (cells_of front @ (c :: cells_of back)));
  epl_in head p (cells_of front @ (c :: cells_of back));
}

ghost
fn ring_ix_close_cons (#a: Type0) (ipl: ipayload a) (head: lref) (p: perm)
                      (c: lref) (x: a) (es: list (lref & a))
  requires is_list_ring_with emp_pl head p (c :: cells_of es)
        ** ipayload_of ipl ((c, x) :: es)
  returns _: unit
  ensures is_list_ring_ix ipl head p ((c, x) :: es)
{
  epl_out head p (c :: cells_of es);
  rewrite (is_list_ring head p (c :: cells_of es))
       as (is_list_ring head p (cells_of ((c, x) :: es)));
  ring_ix_in ipl head p ((c, x) :: es);
}

ghost
fn ring_ix_close_snoc (#a: Type0) (ipl: ipayload a) (head: lref) (p: perm)
                      (es: list (lref & a)) (c: lref) (x: a)
  requires is_list_ring_with emp_pl head p (cells_of es @ [c])
        ** ipayload_of ipl (es @ [(c, x)])
  returns _: unit
  ensures is_list_ring_ix ipl head p (es @ [(c, x)])
{
  epl_out head p (cells_of es @ [c]);
  cells_of_split es [] c x;
  cells_of_nil #a ();
  rewrite (is_list_ring head p (cells_of es @ [c]))
       as (is_list_ring head p (cells_of (es @ [(c, x)])));
  ring_ix_in ipl head p (es @ [(c, x)]);
}

ghost
fn ring_ix_close_at (#a: Type0) (ipl: ipayload a) (head: lref) (p: perm)
                    (front back: list (lref & a)) (c: lref) (x: a)
  requires is_list_ring_with emp_pl head p (cells_of front @ (c :: cells_of back))
        ** ipayload_of ipl (front @ ((c, x) :: back))
  returns _: unit
  ensures is_list_ring_ix ipl head p (front @ ((c, x) :: back))
{
  epl_out head p (cells_of front @ (c :: cells_of back));
  cells_of_split front back c x;
  rewrite (is_list_ring head p (cells_of front @ (c :: cells_of back)))
       as (is_list_ring head p (cells_of (front @ ((c, x) :: back))));
  ring_ix_in ipl head p (front @ ((c, x) :: back));
}

ghost
fn ring_ix_open_last (#a: Type0) (ipl: ipayload a) (head: lref) (p: perm)
                     (es: list (lref & a)) (c: lref) (x: a)
  requires is_list_ring_ix ipl head p (es @ [(c, x)])
  returns _: unit
  ensures is_list_ring_with emp_pl head p (cells_of es @ [c])
       ** ipayload_of ipl (es @ [(c, x)])
{
  ring_ix_out ipl head p (es @ [(c, x)]);
  cells_of_split es [] c x;
  cells_of_nil #a ();
  rewrite (is_list_ring head p (cells_of (es @ [(c, x)])))
       as (is_list_ring head p (cells_of es @ [c]));
  epl_in head p (cells_of es @ [c]);
}

ghost
fn ring_ix_close_drop_last (#a: Type0) (ipl: ipayload a) (head: lref) (p: perm)
                           (es: list (lref & a))
  requires is_list_ring_with emp_pl head p (cells_of es @ [])
        ** ipayload_of ipl (es @ [])
  returns _: unit
  ensures is_list_ring_ix ipl head p es
{
  FStar.List.Tot.append_l_nil (cells_of es);
  FStar.List.Tot.append_l_nil es;
  rewrite (ipayload_of ipl (es @ [])) as (ipayload_of ipl es);
  epl_out head p (cells_of es @ []);
  rewrite (is_list_ring head p (cells_of es @ []))
       as (is_list_ring head p (cells_of es));
  ring_ix_in ipl head p es;
}

ghost
fn ring_ix_close_cat (#a: Type0) (ipl: ipayload a) (head: lref) (p: perm)
                     (front back: list (lref & a))
  requires is_list_ring_with emp_pl head p (cells_of front @ cells_of back)
        ** ipayload_of ipl (front @ back)
  returns _: unit
  ensures is_list_ring_ix ipl head p (front @ back)
{
  epl_out head p (cells_of front @ cells_of back);
  rewrite (is_list_ring head p (cells_of front @ cells_of back))
       as (is_list_ring head p (cells_of (front @ back)));
  ring_ix_in ipl head p (front @ back);
}

ghost
fn rec ipayload_of_split (#a: Type0) (ipl: ipayload a) (u v: list (lref & a))
  requires ipayload_of ipl (u @ v)
  returns _: unit
  ensures ipayload_of ipl u ** ipayload_of ipl v
  decreases u
{
  match u {
    Nil -> {
      rewrite (ipayload_of ipl (u @ v)) as (ipayload_of ipl v);
      fold (ipayload_of ipl (Nil #(lref & a)));
      rewrite (ipayload_of ipl (Nil #(lref & a))) as (ipayload_of ipl u);
    }
    Cons u0 ut -> {
      rewrite (ipayload_of ipl (u @ v)) as (ipayload_of ipl (u0 :: (ut @ v)));
      unfold (ipayload_of ipl (u0 :: (ut @ v)));
      ipayload_of_split ipl ut v;
      fold (ipayload_of ipl (u0 :: ut));
      rewrite (ipayload_of ipl (u0 :: ut)) as (ipayload_of ipl u);
    }
  }
}

ghost
fn rec ipayload_of_join (#a: Type0) (ipl: ipayload a) (u v: list (lref & a))
  requires ipayload_of ipl u ** ipayload_of ipl v
  returns _: unit
  ensures ipayload_of ipl (u @ v)
  decreases u
{
  match u {
    Nil -> {
      rewrite (ipayload_of ipl u) as (ipayload_of ipl (Nil #(lref & a)));
      unfold (ipayload_of ipl (Nil #(lref & a)));
      rewrite (ipayload_of ipl v) as (ipayload_of ipl (u @ v));
    }
    Cons u0 ut -> {
      rewrite (ipayload_of ipl u) as (ipayload_of ipl (u0 :: ut));
      unfold (ipayload_of ipl (u0 :: ut));
      ipayload_of_join ipl ut v;
      fold (ipayload_of ipl (u0 :: (ut @ v)));
      rewrite (ipayload_of ipl (u0 :: (ut @ v))) as (ipayload_of ipl (u @ v));
    }
  }
}

ghost
fn ipayload_of_single_in (#a: Type0) (ipl: ipayload a) (c: lref) (x: a)
  requires ipl c x
  returns _: unit
  ensures ipayload_of ipl [(c, x)]
{
  fold (ipayload_of ipl (Nil #(lref & a)));
  fold (ipayload_of ipl [(c, x)]);
}

ghost
fn ipayload_of_single_out (#a: Type0) (ipl: ipayload a) (c: lref) (x: a)
  requires ipayload_of ipl [(c, x)]
  returns _: unit
  ensures ipl c x
{
  unfold (ipayload_of ipl [(c, x)]);
  unfold (ipayload_of ipl (Nil #(lref & a)));
}

ghost
fn ipayload_of_cons_in (#a: Type0) (ipl: ipayload a) (c: lref) (x: a)
                       (es: list (lref & a))
  requires ipl c x ** ipayload_of ipl es
  returns _: unit
  ensures ipayload_of ipl ((c, x) :: es)
{
  fold (ipayload_of ipl ((c, x) :: es));
}

ghost
fn ipayload_of_cons_out (#a: Type0) (ipl: ipayload a) (c: lref) (x: a)
                        (es: list (lref & a))
  requires ipayload_of ipl ((c, x) :: es)
  returns _: unit
  ensures ipl c x ** ipayload_of ipl es
{
  unfold (ipayload_of ipl ((c, x) :: es));
}

ghost
fn ipayload_of_insert (#a: Type0) (ipl: ipayload a) (front back: list (lref & a))
                      (c: lref) (x: a)
  requires ipayload_of ipl (front @ back) ** ipl c x
  returns _: unit
  ensures ipayload_of ipl (front @ ((c, x) :: back))
{
  ipayload_of_split ipl front back;
  fold (ipayload_of ipl ((c, x) :: back));
  ipayload_of_join ipl front ((c, x) :: back);
}

ghost
fn ipayload_of_remove (#a: Type0) (ipl: ipayload a) (front back: list (lref & a))
                      (c: lref) (x: a)
  requires ipayload_of ipl (front @ ((c, x) :: back))
  returns _: unit
  ensures ipayload_of ipl (front @ back) ** ipl c x
{
  ipayload_of_split ipl front ((c, x) :: back);
  unfold (ipayload_of ipl ((c, x) :: back));
  ipayload_of_join ipl front back;
}

ghost
fn ix_add_del_roundtrip (#a: Type0) (ipl: ipayload a) (front back: list (lref & a))
                        (c: lref) (x: a)
  requires ipayload_of ipl (front @ back) ** ipl c x
  returns _: unit
  ensures ipayload_of ipl (front @ back) ** ipl c x
{
  ipayload_of_insert ipl front back c x;
  ipayload_of_remove ipl front back c x;
}

ghost
fn ix_pin (#a: Type0) (ipl: ipayload a) (front back: list (lref & a)) (c: lref) (x: a)
  requires ipayload_of ipl (front @ ((c, x) :: back))
  returns _: unit
  ensures ipl c x **
          T.trade (ipl c x) (ipayload_of ipl (front @ ((c, x) :: back)))
{
  ipayload_of_remove ipl front back c x;
  intro (T.trade (ipl c x) (ipayload_of ipl (front @ ((c, x) :: back))))
    #(ipayload_of ipl (front @ back))
    fn _ {
      ipayload_of_insert ipl front back c x;
    };
}

ghost
fn ix_unpin (#a: Type0) (ipl: ipayload a) (front back: list (lref & a)) (c: lref) (x: a)
  requires ipl c x **
           T.trade (ipl c x) (ipayload_of ipl (front @ ((c, x) :: back)))
  returns _: unit
  ensures ipayload_of ipl (front @ ((c, x) :: back))
{
  T.elim_trade (ipl c x) (ipayload_of ipl (front @ ((c, x) :: back)));
}

ghost
fn ix_repin (#a: Type0) (ipl: ipayload a) (front back: list (lref & a)) (c: lref) (x: a)
  requires ipayload_of ipl (front @ ((c, x) :: back))
  returns _: unit
  ensures ipl c x **
          (forall* (y: a).
             T.trade (ipl c y) (ipayload_of ipl (front @ ((c, y) :: back))))
{
  ipayload_of_remove ipl front back c x;
  intro (forall* (y: a).
           T.trade (ipl c y) (ipayload_of ipl (front @ ((c, y) :: back))))
    #(ipayload_of ipl (front @ back))
    fn _ y {
      ipayload_of_insert ipl front back c y;
    };
}

unfold let ipl_of_payload (pl: payload) : ipayload unit = fun c _ -> pl c

let rec unitize (cs: list lref)
  : Tot (list (lref & unit)) (decreases cs)
  = match cs with
    | [] -> []
    | c :: tl -> (c, ()) :: unitize tl

let rec cells_of_unitize (cs: list lref)
  : Lemma (ensures cells_of (unitize cs) == cs) (decreases cs)
          [SMTPat (cells_of (unitize cs))]
  = match cs with
    | [] -> ()
    | _ :: tl -> cells_of_unitize tl

ghost
fn rec payload_of_to_ix (pl: payload) (cs: list lref)
  requires payload_of pl cs
  returns _: unit
  ensures ipayload_of (ipl_of_payload pl) (unitize cs)
  decreases cs
{
  match cs {
    Nil -> {
      rewrite (payload_of pl cs) as (payload_of pl (Nil #lref));
      unfold (payload_of pl (Nil #lref));
      fold (ipayload_of (ipl_of_payload pl) (Nil #(lref & unit)));
      rewrite (ipayload_of (ipl_of_payload pl) (Nil #(lref & unit)))
           as (ipayload_of (ipl_of_payload pl) (unitize cs));
    }
    Cons c0 ct -> {
      rewrite (payload_of pl cs) as (payload_of pl (c0 :: ct));
      unfold (payload_of pl (c0 :: ct));
      payload_of_to_ix pl ct;
      fold (ipayload_of (ipl_of_payload pl) ((c0, ()) :: unitize ct));
      rewrite (ipayload_of (ipl_of_payload pl) ((c0, ()) :: unitize ct))
           as (ipayload_of (ipl_of_payload pl) (unitize cs));
    }
  }
}

ghost
fn rec payload_of_from_ix (pl: payload) (cs: list lref)
  requires ipayload_of (ipl_of_payload pl) (unitize cs)
  returns _: unit
  ensures payload_of pl cs
  decreases cs
{
  match cs {
    Nil -> {
      rewrite (ipayload_of (ipl_of_payload pl) (unitize cs))
           as (ipayload_of (ipl_of_payload pl) (Nil #(lref & unit)));
      unfold (ipayload_of (ipl_of_payload pl) (Nil #(lref & unit)));
      fold (payload_of pl (Nil #lref));
      rewrite (payload_of pl (Nil #lref)) as (payload_of pl cs);
    }
    Cons c0 ct -> {
      rewrite (ipayload_of (ipl_of_payload pl) (unitize cs))
           as (ipayload_of (ipl_of_payload pl) ((c0, ()) :: unitize ct));
      unfold (ipayload_of (ipl_of_payload pl) ((c0, ()) :: unitize ct));
      payload_of_from_ix pl ct;
      fold (payload_of pl (c0 :: ct));
      rewrite (payload_of pl (c0 :: ct)) as (payload_of pl cs);
    }
  }
}

ghost
fn seg_with_to_ix (pl: payload) (prev cur endl: lref) (p: perm) (cs: list lref)
  requires is_list_seg_with pl prev cur endl p cs
  returns _: unit
  ensures is_list_seg_ix (ipl_of_payload pl) prev cur endl p (unitize cs)
{
  seg_pl_out pl prev cur endl p cs;
  payload_of_to_ix pl cs;
  rewrite (is_list_seg_with no_payload prev cur endl p cs)
       as (is_list_seg prev cur endl p (cells_of (unitize cs)));
  fold (is_list_seg_ix (ipl_of_payload pl) prev cur endl p (unitize cs));
}

ghost
fn seg_ix_to_with (pl: payload) (prev cur endl: lref) (p: perm) (cs: list lref)
  requires is_list_seg_ix (ipl_of_payload pl) prev cur endl p (unitize cs)
  returns _: unit
  ensures is_list_seg_with pl prev cur endl p cs
{
  unfold (is_list_seg_ix (ipl_of_payload pl) prev cur endl p (unitize cs));
  rewrite (is_list_seg prev cur endl p (cells_of (unitize cs)))
       as (is_list_seg_with no_payload prev cur endl p cs);
  payload_of_from_ix pl cs;
  seg_pl_in pl prev cur endl p cs;
}

ghost
fn ring_with_to_ix (pl: payload) (head: lref) (p: perm) (cs: list lref)
  requires is_list_ring_with pl head p cs
  returns _: unit
  ensures is_list_ring_ix (ipl_of_payload pl) head p (unitize cs)
{
  ring_pl_out pl head p cs;
  payload_of_to_ix pl cs;
  rewrite (is_list_ring_with no_payload head p cs)
       as (is_list_ring head p (cells_of (unitize cs)));
  fold (is_list_ring_ix (ipl_of_payload pl) head p (unitize cs));
}

ghost
fn ring_ix_to_with (pl: payload) (head: lref) (p: perm) (cs: list lref)
  requires is_list_ring_ix (ipl_of_payload pl) head p (unitize cs)
  returns _: unit
  ensures is_list_ring_with pl head p cs
{
  unfold (is_list_ring_ix (ipl_of_payload pl) head p (unitize cs));
  rewrite (is_list_ring head p (cells_of (unitize cs)))
       as (is_list_ring_with no_payload head p cs);
  payload_of_from_ix pl cs;
  ring_pl_in pl head p cs;
}

ghost
fn seg_to_ix (prev cur endl: lref) (p: perm) (cs: list lref)
  requires is_list_seg prev cur endl p cs
  returns _: unit
  ensures is_list_seg_ix (ipl_of_payload no_payload) prev cur endl p (unitize cs)
{
  seg_with_to_ix no_payload prev cur endl p cs;
}

ghost
fn seg_from_ix (prev cur endl: lref) (p: perm) (cs: list lref)
  requires is_list_seg_ix (ipl_of_payload no_payload) prev cur endl p (unitize cs)
  returns _: unit
  ensures is_list_seg prev cur endl p cs
{
  seg_ix_to_with no_payload prev cur endl p cs;
}

ghost
fn ring_to_ix (head: lref) (p: perm) (cs: list lref)
  requires is_list_ring head p cs
  returns _: unit
  ensures is_list_ring_ix (ipl_of_payload no_payload) head p (unitize cs)
{
  ring_with_to_ix no_payload head p cs;
}

ghost
fn ring_from_ix (head: lref) (p: perm) (cs: list lref)
  requires is_list_ring_ix (ipl_of_payload no_payload) head p (unitize cs)
  returns _: unit
  ensures is_list_ring head p cs
{
  ring_ix_to_with no_payload head p cs;
}

let del_prev_rest (head prev next ent: lref) (front back: list lref) (nx pp: lref) : slprop =
  match front, back with
  | [], [] ->
    pure (prev == head /\ next == head /\ nx == ent /\ ent =!= head /\ pp == ent)
  | [], b0 :: bt ->
    exists* (vn: L.struct_list_node).
      R.pts_to next #1.0R vn **
      is_list_seg next nx head 1.0R bt **
      pure (prev == head /\ next == b0 /\ next =!= head /\ ent =!= head) **
      pure (lprev vn == ent /\ lnext vn == nx) **
      pure (pp == last_or head back)
  | f0 :: ft, [] ->
    exists* (vh: L.struct_list_node).
      R.pts_to head #1.0R vh **
      is_list_seg_s head (lnext vh) prev head 1.0R (finit (f0 :: ft)) **
      pure (next == head /\ prev == flast (f0 :: ft) /\ prev =!= head /\ ent =!= head) **
      pure (lprev vh == ent /\ lnext vh == nx) **
      pure (pp == last_or head (finit (f0 :: ft)))
  | f0 :: ft, b0 :: bt ->
    exists* (vh: L.struct_list_node) (vn: L.struct_list_node).
      R.pts_to head #1.0R vh **
      R.pts_to next #1.0R vn **
      is_list_seg_s head (lnext vh) prev head 1.0R (finit (f0 :: ft)) **
      is_list_seg next nx head 1.0R bt **
      pure (prev == flast (f0 :: ft) /\ prev =!= head /\ ent =!= head) **
      pure (next == b0 /\ next =!= head) **
      pure (lprev vn == ent /\ lnext vn == nx) **
      pure (lprev vh == last_or head back) **
      pure (pp == last_or head (finit (f0 :: ft)))

ghost
fn del_reseat_old (head prev next ent: lref) (front back: list lref) (#nx: lref)
              (#vn: L.struct_list_node)
  requires
    R.pts_to next #1.0R vn **
    del_rest1 head prev next ent front back nx **
    pure (lprev vn == ent) **
    pure (lnext vn == nx)
  returns _: unit
  ensures
    exists* (vp: L.struct_list_node).
      R.pts_to prev #1.0R vp **
      del_prev_rest head prev next ent front back nx (lprev vp) **
      pure (lnext vp == ent) **
      pure (prev == last_or head front) **
      pure (next == first_or head back) **
      pure ((prev == next) <==> (front @ back == []))
{
  match front {
    Nil -> {
      match back {
        Nil -> {

          rewrite (del_rest1 head prev next ent front back nx)
               as (del_rest1 head prev next ent (Nil #lref) (Nil #lref) nx);
          unfold (del_rest1 head prev next ent (Nil #lref) (Nil #lref) nx);
          unfold (is_list_seg_s_with no_payload head nx ent head 1.0R (Nil #lref));
          rewrite (R.pts_to next #1.0R vn) as (R.pts_to prev #1.0R vn);
          fold (del_prev_rest head prev next ent (Nil #lref) (Nil #lref) nx (lprev vn));
          rewrite (del_prev_rest head prev next ent (Nil #lref) (Nil #lref) nx (lprev vn))
               as (del_prev_rest head prev next ent front back nx (lprev vn));
        }
        Cons b0 bt -> {

          rewrite (del_rest1 head prev next ent front back nx)
               as (del_rest1 head prev next ent (Nil #lref) (b0 :: bt) nx);
          unfold (del_rest1 head prev next ent (Nil #lref) (b0 :: bt) nx);
          with hv. assert (R.pts_to head #1.0R hv);
          unfold (is_list_seg_s_with no_payload head (lnext hv) ent head 1.0R (Nil #lref));
          rewrite (R.pts_to head #1.0R hv) as (R.pts_to prev #1.0R hv);
          refs_distinct prev next;
          fold (del_prev_rest head prev next ent (Nil #lref) (b0 :: bt) nx (lprev hv));
          rewrite (del_prev_rest head prev next ent (Nil #lref) (b0 :: bt) nx (lprev hv))
               as (del_prev_rest head prev next ent front back nx (lprev hv));
        }
      }
    }
    Cons f0 ft -> {
      last_or_flast head front;
      finit_flast_append front;
      match back {
        Nil -> {

          rewrite (del_rest1 head prev next ent front back nx)
               as (del_rest1 head prev next ent (f0 :: ft) (Nil #lref) nx);
          unfold (del_rest1 head prev next ent (f0 :: ft) (Nil #lref) nx);
          rewrite (R.pts_to next #1.0R vn) as (R.pts_to head #1.0R vn);
          rewrite (is_list_seg_s_with no_payload head nx ent head 1.0R (f0 :: ft))
               as (is_list_seg_s_with no_payload head nx ent head 1.0R
                     (finit (f0 :: ft) @ [flast (f0 :: ft)]));
          seg_s_peel_last no_payload head nx ent head
                          (finit (f0 :: ft)) (flast (f0 :: ft));
          with vl. assert (R.pts_to (flast (f0 :: ft)) #1.0R vl);
          rewrite (R.pts_to (flast (f0 :: ft)) #1.0R vl) as (R.pts_to prev #1.0R vl);
          rewrite (is_list_seg_s_with no_payload head nx (flast (f0 :: ft)) head 1.0R
                     (finit (f0 :: ft)))
               as (is_list_seg_s_with no_payload head (lnext vn) prev head 1.0R
                     (finit (f0 :: ft)));
          refs_distinct prev head;
          fold (del_prev_rest head prev next ent (f0 :: ft) (Nil #lref) nx (lprev vl));
          rewrite (del_prev_rest head prev next ent (f0 :: ft) (Nil #lref) nx (lprev vl))
               as (del_prev_rest head prev next ent front back nx (lprev vl));
        }
        Cons b0 bt -> {
          rewrite (del_rest1 head prev next ent front back nx)
               as (del_rest1 head prev next ent (f0 :: ft) (b0 :: bt) nx);
          unfold (del_rest1 head prev next ent (f0 :: ft) (b0 :: bt) nx);
          with hv. assert (R.pts_to head #1.0R hv);
          rewrite (is_list_seg_s_with no_payload head (lnext hv) ent head 1.0R (f0 :: ft))
               as (is_list_seg_s_with no_payload head (lnext hv) ent head 1.0R
                     (finit (f0 :: ft) @ [flast (f0 :: ft)]));
          seg_s_peel_last no_payload head (lnext hv) ent head
                          (finit (f0 :: ft)) (flast (f0 :: ft));
          with vl. assert (R.pts_to (flast (f0 :: ft)) #1.0R vl);
          rewrite (R.pts_to (flast (f0 :: ft)) #1.0R vl) as (R.pts_to prev #1.0R vl);
          rewrite (is_list_seg_s_with no_payload head (lnext hv) (flast (f0 :: ft)) head
                     1.0R (finit (f0 :: ft)))
               as (is_list_seg_s_with no_payload head (lnext hv) prev head 1.0R
                     (finit (f0 :: ft)));
          refs_distinct prev head;
          refs_distinct prev next;
          fold (del_prev_rest head prev next ent (f0 :: ft) (b0 :: bt) nx (lprev vl));
          rewrite (del_prev_rest head prev next ent (f0 :: ft) (b0 :: bt) nx (lprev vl))
               as (del_prev_rest head prev next ent front back nx (lprev vl));
        }
      }
    }
  }
}

ghost
fn del_expose_prev (head prev next ent: lref) (front back: list lref)
  requires del_cut head prev next ent front back
  returns _: unit
  ensures
    exists* (vp: L.struct_list_node) (nx: lref).
      R.pts_to prev vp **
      del_prev_rest head prev next ent front back nx (lprev vp) **
      pure (lnext vp == ent) **
      pure (prev == last_or head front) **
      pure (next == first_or head back) **
      pure ((prev == next) <==> (front @ back == []))
{
  del_expose_next head prev next ent front back;
  del_reseat_old head prev next ent front back;
}

(* After updating the predecessor, only the successor's backward link remains. *)
let del_next_rest (head prev next ent: lref) (front back: list lref) (nx: lref) : slprop =
  match front, back with
  | [], [] ->
    pure (prev == head /\ next == head /\ nx == head /\ ent =!= head)
  | [], b0 :: bt ->
    exists* (vp: L.struct_list_node).
      R.pts_to prev vp **
      is_list_seg next nx head 1.0R bt **
      pure (prev == head /\ next == b0 /\ next =!= head /\ ent =!= head) **
      pure (lnext vp == next /\ lprev vp == last_or head back)
  | f0 :: ft, [] ->
    exists* (vp: L.struct_list_node).
      R.pts_to prev vp **
      is_list_seg_s head nx prev head 1.0R (finit (f0 :: ft)) **
      pure (next == head /\ prev == flast (f0 :: ft) /\ prev =!= head /\ ent =!= head) **
      pure (lnext vp == next /\ lprev vp == last_or head (finit (f0 :: ft)))
  | f0 :: ft, b0 :: bt ->
    exists* (vh vp: L.struct_list_node).
      R.pts_to head vh **
      R.pts_to prev vp **
      is_list_seg_s head (lnext vh) prev head 1.0R (finit (f0 :: ft)) **
      is_list_seg next nx head 1.0R bt **
      pure (prev == flast (f0 :: ft) /\ prev =!= head /\ ent =!= head) **
      pure (next == b0 /\ next =!= head) **
      pure (lnext vp == next /\ lprev vp == last_or head (finit (f0 :: ft))) **
      pure (lprev vh == last_or head back)

ghost
fn del_reseat_next (head prev next ent: lref) (front back: list lref)
                   (#nx #pp: lref) (#vp: L.struct_list_node)
  requires
    R.pts_to prev vp ** del_prev_rest head prev next ent front back nx pp **
    pure (lnext vp == next) ** pure (lprev vp == pp)
  returns _: unit
  ensures
    exists* (vn: L.struct_list_node).
      R.pts_to next vn **
      del_next_rest head prev next ent front back (lnext vn)
{
  match front {
    Nil -> {
      match back {
        Nil -> {
          unfold (del_prev_rest head prev next ent front back nx pp);
          rewrite (R.pts_to prev vp) as (R.pts_to next vp);
          fold (del_next_rest head prev next ent front back (lnext vp));
        }
        Cons b0 bt -> {
          unfold (del_prev_rest head prev next ent front back nx pp);
          with vn. assert (R.pts_to next vn);
          rewrite (is_list_seg next nx head 1.0R bt)
               as (is_list_seg next (lnext vn) head 1.0R bt);
          fold (del_next_rest head prev next ent front back (lnext vn));
        }
      }
    }
    Cons f0 ft -> {
      match back {
        Nil -> {
          unfold (del_prev_rest head prev next ent front back nx pp);
          with vh. assert (R.pts_to head vh);
          rewrite (R.pts_to head vh) as (R.pts_to next vh);
          fold (del_next_rest head prev next ent front back (lnext vh));
        }
        Cons b0 bt -> {
          unfold (del_prev_rest head prev next ent front back nx pp);
          with vn. assert (R.pts_to next vn);
          rewrite (is_list_seg next nx head 1.0R bt)
               as (is_list_seg next (lnext vn) head 1.0R bt);
          fold (del_next_rest head prev next ent front back (lnext vn));
        }
      }
    }
  }
}

ghost
fn del_close_next (head prev next ent: lref) (front back: list lref)
                  (#nx: lref) (#vn: L.struct_list_node)
  requires
    R.pts_to next vn ** del_next_rest head prev next ent front back nx **
    pure (lnext vn == nx) ** pure (lprev vn == prev)
  returns _: unit
  ensures is_list_ring head 1.0R (front @ back)
{
  match front {
    Nil -> {
      match back {
        Nil -> {
          unfold (del_next_rest head prev next ent front back nx);
          rewrite (R.pts_to next vn) as (R.pts_to head vn);
          ring_intro_empty no_payload head;
        }
        Cons b0 bt -> {
          unfold (del_next_rest head prev next ent front back nx);
          with vp. assert (R.pts_to prev vp);
          fold (del_rest2 head prev next ent front back nx (lprev vp));
          del_close head prev next ent front back;
        }
      }
    }
    Cons f0 ft -> {
      match back {
        Nil -> {
          unfold (del_next_rest head prev next ent front back nx);
          with vp. assert (R.pts_to prev vp);
          rewrite (R.pts_to next vn) as (R.pts_to head vn);
          rewrite (is_list_seg_s head nx prev head 1.0R (finit (f0 :: ft)))
               as (is_list_seg_s head (lnext vn) prev head 1.0R (finit (f0 :: ft)));
          fold (del_rest2 head prev next ent front back nx (lprev vp));
          del_close head prev next ent front back;
        }
        Cons b0 bt -> {
          unfold (del_next_rest head prev next ent front back nx);
          with vp. assert (R.pts_to prev vp);
          fold (del_rest2 head prev next ent front back nx (lprev vp));
          del_close head prev next ent front back;
        }
      }
    }
  }
}
