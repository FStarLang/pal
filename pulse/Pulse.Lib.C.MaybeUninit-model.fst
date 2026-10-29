module Pulse.Lib.C.MaybeUninit
friend Pulse.Lib.Reference
#lang-pulse
open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Ghost
open Pulse.Class.PtsTo
open Pulse.Lib.Array.Core
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array.Core
module SizeT = FStar.SizeT

// A one-element sequence, the mask-slot backing a single borrowed cell.
let singleton #a (x: a) : Seq.seq a = Seq.create 1 x
let singleton_inj #a (x: a) : Lemma (Seq.index (singleton x) 0 == x) [SMTPat (singleton x)] = ()
let upd_singleton #a (x y: a) :
    Lemma (Seq.upd (singleton x) 0 y == singleton y)
      [SMTPat (Seq.upd (singleton x) 0 y)] =
  assert Seq.equal (Seq.upd (singleton x) 0 y) (singleton y)

// The mask representation: [pts_to_maybe_uninit r v] records the (optional) cell
// value [v] as the single mask slot, uniformly covering both the initialized
// ([Some]) and uninitialized ([None]) cases, so a cell can be borrowed without a
// run-time branch on its initialization state. Mirrors the internal models of
// [R.pts_to] / [R.pts_to_uninit], which is why the implementation friends
// [Pulse.Lib.Reference].
let pts_to_maybe_uninit (#a: Type u#a) ([@@@mkey]r: R.ref a) (v: option a) : slprop =
  exists* s. pure (Seq.length s == 1 /\ Seq.index s 0 == v) ** A.pts_to_mask r s (fun _ -> True)

let pts_to_maybe_uninit_timeless r v = assert_norm (timeless (pts_to_maybe_uninit r v))

[@@pulse_intro]
ghost fn reveal_maybe u#a (#a: Type u#a) (r: R.ref a) (#v: option a { Some? v })
  requires pts_to_maybe_uninit r v
  ensures R.pts_to r (Some?.v v)
{
  unfold pts_to_maybe_uninit r v;
  fold R.pts_to r #1.0R (Some?.v v);
}

[@@pulse_intro]
ghost fn intro_maybe_some u#a (#a: Type u#a) (r: R.ref a) (#x: a)
  requires R.pts_to r x
  ensures pts_to_maybe_uninit r (Some x)
{
  unfold R.pts_to r x;
  fold pts_to_maybe_uninit r (Some x);
}

[@@pulse_intro]
ghost fn forget_maybe u#a (#a: Type u#a) (r: R.ref a) (#v: option a)
  requires pts_to_maybe_uninit r v
  ensures R.pts_to_uninit r
{
  unfold pts_to_maybe_uninit r v;
  with s. assert A.pts_to_mask r s (fun _ -> True);
  fold R.pts_to_uninit r;
}

unobservable
fn array_at_maybe u#a (#a: Type u#a) (arr: array a) (i: SizeT.t)
    (#v: erased (Seq.seq (option a)) { SizeT.v i < length arr /\ length arr == Seq.length v }) #mask
  requires pts_to_mask arr v mask
  requires pure (mask (SizeT.v i))
  returns r: R.ref a
  ensures rewrites_to r (R.array_at_ghost arr (SizeT.v i))
  ensures pts_to_maybe_uninit r (Seq.index v (SizeT.v i))
  ensures pts_to_mask arr v (fun k -> mask k /\ k <> SizeT.v i)
{
  let res = sub arr i (SizeT.v i + 1);
  mask_ext res (singleton (Seq.index v (SizeT.v i))) (fun _ -> True);
  fold pts_to_maybe_uninit res (Seq.index v (SizeT.v i));
  mask_mext arr (fun k -> mask k /\ k <> SizeT.v i);
  res
}

ghost
fn return_array_at_maybe u#a (#a: Type u#a) (arr: array a) (i: nat) (#w: option a) (#v': Seq.seq (option a) { i < length arr /\ length arr == Seq.length v' }) (#mask: nat->prop)
  requires pts_to_maybe_uninit (R.array_at_ghost arr i) w
  requires pts_to_mask arr v' mask
  requires pure (~(mask i))
  ensures pts_to_mask arr (Seq.upd v' i w) (fun k -> mask k \/ k == i)
{
  unfold pts_to_maybe_uninit (R.array_at_ghost arr i) w;
  with s. assert A.pts_to_mask (R.array_at_ghost arr i) s _;
  gsub_elim arr i (i+1);
  join_mask arr;
  mask_ext arr (Seq.upd v' i (Seq.index s 0)) (fun k -> mask k \/ k == i);
}
