module Pulse.Lib.C.MaybeUninit
#lang-pulse
open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Ghost
open Pulse.Class.PtsTo
open Pulse.Lib.Array.Core
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array.Core
module SizeT = FStar.SizeT

// ---------------------------------------------------------------------------
// Deferred-initialization ("maybe uninitialized") ownership of a single
// reference, and the array-cell borrow/return that produces it.
//
// This is a thin extension of `Pulse.Lib.Reference`: it is the *only* place PAL
// depends on the mask representation of `Pulse.Lib.Reference.ref` (`ref = array`,
// borrowing a cell is a `sub` + mask reshape). Because that identity is private
// to `Pulse.Lib.Reference`, the implementation `friend`s it; the interface below
// exposes just the maybe-cell view PAL needs, so the rest of PAL only ever sees
// this public API and never the `Reference` internals.
// ---------------------------------------------------------------------------

(* Deferred-initialization ownership of a single reference. A cell that has been
   borrowed without committing up front to whether it was initialized is owned as
   [pts_to_maybe_uninit r v]: [Some x] is a readable cell holding [x] (equivalent
   to [R.pts_to r x]), [None] is a write-only uninitialized cell (equivalent to
   [R.pts_to_uninit r]). This is the common label for the results of [R.array_at]
   and [R.array_at_uninit] (see [array_at_maybe]); use [reveal_maybe]/
   [intro_maybe_some] to move between the readable view and [forget_maybe] to drop
   the value. *)
val pts_to_maybe_uninit (#[@@@mkey]a: Type u#a) ([@@@mkey]r: R.ref a) (v: option a) : slprop

val pts_to_maybe_uninit_timeless (#a: Type u#a) (r: R.ref a) (v: option a)
  : Lemma (timeless (pts_to_maybe_uninit r v))
          [SMTPat (timeless (pts_to_maybe_uninit r v))]

(* Recover the readable [R.pts_to] of a maybe-initialized cell known to hold a
   value. The cell's optional value [v] is taken directly, refined by [Some? v],
   rather than being matched structurally as [Some x]: this way the
   [pts_to_maybe_uninit r v] resource unifies syntactically against whatever value
   is in context and the [Some?] obligation is discharged by SMT, which keeps
   automatic resolution robust. Tagged [pulse_intro] so Pulse applies it whenever
   a maybe-cell known to be initialized flows into a readable position. *)
[@@pulse_intro]
ghost fn reveal_maybe u#a (#a: Type u#a) (r: R.ref a) (#v: option a { Some? v })
  requires pts_to_maybe_uninit r v
  ensures R.pts_to r (Some?.v v)

(* The reverse of [reveal_maybe]: label a readable cell as maybe-initialized.
   Tagged [pulse_intro] so Pulse applies it automatically wherever a
   [pts_to_maybe_uninit r (Some x)] is needed and a readable [R.pts_to r x] is
   available -- e.g. to hand a cell just written through a plain [ref] back to
   the array it was borrowed from. It does not clash with its inverse
   [reveal_maybe]: the two produce different resources ([pts_to_maybe_uninit]
   here vs [R.pts_to] there), so goal-directed resolution only ever picks one
   for a given target. *)
[@@pulse_intro]
ghost fn intro_maybe_some u#a (#a: Type u#a) (r: R.ref a) (#x: a)
  requires R.pts_to r x
  ensures pts_to_maybe_uninit r (Some x)

(* Forget the value of a maybe-initialized cell, recovering the write-only
   [R.pts_to_uninit]. Tagged [pulse_intro] so Pulse applies it automatically
   wherever a [R.pts_to_uninit r] is needed and a [pts_to_maybe_uninit r v] is
   available (matching [v] syntactically for any value, initialized or not). It
   does not clash with [reveal_maybe]: the two produce different resources
   ([R.pts_to_uninit] here vs [R.pts_to] there), so goal-directed resolution only
   ever picks one for a given target. *)
[@@pulse_intro]
ghost fn forget_maybe u#a (#a: Type u#a) (r: R.ref a) (#v: option a)
  requires pts_to_maybe_uninit r v
  ensures R.pts_to_uninit r

(* Borrow cell [i] of [arr] as a [ref], for any initialization state: the cell is
   handed back as [pts_to_maybe_uninit] carrying its current value ([Some x] if it
   was initialized, [None] otherwise). This is the common generalization of
   [R.array_at] (the initialized projection) and [R.array_at_uninit] (the
   value-forgetting projection): the executable carve is identical, only the
   resulting ownership differs, so no run-time branch on the (ghost)
   initialization state is needed. Requires full permission, because the
   uninitialized case yields a writable, full-permission cell. *)
unobservable
fn array_at_maybe u#a (#a: Type u#a) (arr: array a) (i: SizeT.t)
    (#v: erased (Seq.seq (option a)) { SizeT.v i < length arr /\ length arr == Seq.length v }) #mask
  requires pts_to_mask arr v mask
  requires pure (mask (SizeT.v i))
  returns r: R.ref a
  ensures rewrites_to r (R.array_at_ghost arr (SizeT.v i))
  ensures pts_to_maybe_uninit r (Seq.index v (SizeT.v i))
  ensures pts_to_mask arr v (fun k -> mask k /\ k <> SizeT.v i)

(* Return a cell borrowed with [array_at_maybe], writing its optional value [w]
   back into slot [i], so [Some x] restores an initialized cell and [None] an
   uninitialized one, in a single lemma and without the [full_mask] side condition
   the value-forgetting return needs. Dual of [array_at_maybe]. *)
ghost
fn return_array_at_maybe u#a (#a: Type u#a) (arr: array a) (i: nat) (#w: option a) (#v': Seq.seq (option a) { i < length arr /\ length arr == Seq.length v' }) (#mask: nat->prop)
  requires pts_to_maybe_uninit (R.array_at_ghost arr i) w
  requires pts_to_mask arr v' mask
  requires pure (~(mask i))
  ensures pts_to_mask arr (Seq.upd v' i w) (fun k -> mask k \/ k == i)
