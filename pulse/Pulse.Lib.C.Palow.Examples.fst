module Pulse.Lib.C.Palow.Examples

(* ---------------------------------------------------------------------------
   What the translator has to emit.

   These are hand-written Palow renditions of programs PAL already translates,
   written the way the generated code will look once milestone 2 lands. They
   are here to pin the target down before the translator changes, and to check
   that the pieces compose: a pointer parameter is a `ptr` and nothing else,
   ownership is a `t_pts_to`, a dereference is a `t_read`, an assignment is a
   `t_write`, and a local is a stack allocation.

   Three things are worth comparing against what PAL emits today:

   - `int *x` translates to `ptr`, not `ref Int32.t`. The F* *type* of a
     parameter no longer depends on how the pointer is used, which is what
     removes the pointer-kind inference in `src/pass/elab.rs`.
   - There is no `let mut` shadowing of parameters. Today every parameter is
     rebound as a Pulse local so that assignment to it works; here a local is
     an explicit `stack_alloc`/`stack_free` pair, so a parameter that is never
     assigned costs nothing.
   - Nested dereference works by `rewrites_to`, with no ghost step in between:
     `read_nested` is three lines and the inner pointer resolves the outer
     points-to on its own.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes
open Pulse.Lib.C.Palow.Machine
open Pulse.Lib.C.Palow.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32

module I32 = FStar.Int32

(* test/swap/swap.c:

     void swap(int *x, int *y)
       _ensures( *y == _old( *x) && *x == _old( *y))
     { int tmp = *y; *y = *x; *x = tmp; }

   The postcondition is the specification rather than a `with_pure` afterthought,
   because the points-to predicate now carries the value. *)
fn swap (x y: ptr) (#a #b: erased I32.t)
  requires int32_t_pts_to x 1.0R a ** int32_t_pts_to y 1.0R b
  ensures  int32_t_pts_to x 1.0R b ** int32_t_pts_to y 1.0R a
{
  let tmp = int32_t_read y;
  let vx = int32_t_read x;
  int32_t_write y vx;
  int32_t_write x tmp;
}

(* The same, but with `tmp` given a real address, as it would be if the C
   source took `&tmp`. A local is a `stack_alloc`/`stack_free` pair; handing it
   back needs `int32_t_forget`, because deallocation must not care what was
   last stored. *)
fn swap_addressable (x y: ptr) (#a #b: erased I32.t)
  requires int32_t_pts_to x 1.0R a ** int32_t_pts_to y 1.0R b
  ensures  int32_t_pts_to x 1.0R b ** int32_t_pts_to y 1.0R a
{
  let tmp = int32_t_stack_alloc ();
  let vy = int32_t_read y;
  int32_t_write_uninit tmp vy;
  let vx = int32_t_read x;
  int32_t_write y vx;
  let vt = int32_t_read tmp;
  int32_t_write x vt;
  int32_t_forget tmp;
  int32_t_stack_free tmp;
}

(* `**x`. This is the case that forced `rewrites_to` into the read
   postcondition: the pointer read out of `pp` has to be definitionally the
   logical pointee, or the second read cannot find its own points-to. *)
fn read_nested (pp: ptr) (#p: perm) (#q: erased ptr) (#v: erased I32.t)
  preserves ptr_pts_to pp p q
  preserves int32_t_pts_to q 1.0R v
  returns   r : I32.t
  ensures   rewrites_to r (reveal v)
{
  let inner = ptr_read pp;
  int32_t_read inner
}

(* Writing through a nested pointer, which is the assignment counterpart. *)
fn write_nested (pp: ptr) (w: I32.t) (#p: perm) (#q: erased ptr) (#v: erased I32.t)
  preserves ptr_pts_to pp p q
  requires  int32_t_pts_to q 1.0R v
  ensures   int32_t_pts_to q 1.0R w
{
  let inner = ptr_read pp;
  int32_t_write inner w;
}

(* A shared (read-only) parameter, which is what `_plain` / a `const` pointer
   becomes: a fraction rather than full ownership. Nothing about the type
   changes, only the permission, which is the point of dropping the
   `ref`-versus-array-versus-pointer distinction. *)
fn sum_two (x y: ptr) (#px #py: perm) (#a #b: erased I32.t)
  preserves int32_t_pts_to x px a
  preserves int32_t_pts_to y py b
  requires  pure (I32.fits (I32.v a + I32.v b))
  returns   r : I32.t
  ensures   pure (I32.v r == I32.v a + I32.v b)
{
  let va = int32_t_read x;
  let vb = int32_t_read y;
  I32.add va vb
}

(* ---------------------------------------------------------------------------
   Subscripts

   `uint32_t a[]` in C is one pointer with a sequence's worth of ownership, and
   `a[i]` is `array_focus`, a machine operation on the element, and
   `array_unfocus`. This is the shape PAL emits: the offset arithmetic is
   `esize * i` with its `fits` obligation discharged from the ownership itself,
   the element is traded between the generic `elem_pts_to` and the scalar's own
   predicate by the `reveal`/`conceal` pair, and the sequence that comes back
   is `Seq.upd`, which for a read is the identity.
   --------------------------------------------------------------------------- *)

fn array_get (a: ptr) (i: SZ.t) (#p: perm) (#xs: erased (Seq.seq U32.t))
  preserves array_pts_to uint32_t_repr (SZ.v uint32_t_sizeof) a p xs
  requires  pure (SZ.v i < Seq.length xs)
  returns   v : U32.t
  // The precondition is not in scope when the postcondition is typed, and
  // `Seq.index` is partial, so the bound has to be repeated here. This is what
  // the emitter's `guards` mechanism does for a generated contract.
  ensures   pure (SZ.v i < Seq.length xs /\ v == Seq.index xs (SZ.v i))
{
  array_offset_fits uint32_t_repr a uint32_t_sizeof i;
  array_focus uint32_t_repr a uint32_t_sizeof i (uint32_t_sizeof `SZ.mul` i);
  uint32_t_of_elem (a +! (uint32_t_sizeof `SZ.mul` i));
  let v = uint32_t_read (a +! (uint32_t_sizeof `SZ.mul` i));
  uint32_t_to_elem (a +! (uint32_t_sizeof `SZ.mul` i));
  array_unfocus_read uint32_t_repr a uint32_t_sizeof i (uint32_t_sizeof `SZ.mul` i);
  v
}

fn array_set (a: ptr) (i: SZ.t) (w: U32.t) (#xs: erased (Seq.seq U32.t))
  requires array_pts_to uint32_t_repr (SZ.v uint32_t_sizeof) a 1.0R xs
  requires pure (SZ.v i < Seq.length xs)
  // Same story as `array_get`: `Seq.upd` is partial, so the sequence that
  // comes back is named and constrained rather than written out in the slprop.
  ensures  exists* (ys: Seq.seq U32.t).
             array_pts_to uint32_t_repr (SZ.v uint32_t_sizeof) a 1.0R ys **
             pure (SZ.v i < Seq.length xs /\ ys == Seq.upd xs (SZ.v i) w)
{
  array_offset_fits uint32_t_repr a uint32_t_sizeof i;
  array_focus uint32_t_repr a uint32_t_sizeof i (uint32_t_sizeof `SZ.mul` i);
  uint32_t_of_elem (a +! (uint32_t_sizeof `SZ.mul` i));
  uint32_t_write (a +! (uint32_t_sizeof `SZ.mul` i)) w;
  uint32_t_to_elem (a +! (uint32_t_sizeof `SZ.mul` i));
  array_unfocus uint32_t_repr a uint32_t_sizeof i (uint32_t_sizeof `SZ.mul` i);
}

(* ---------------------------------------------------------------------------
   A loop.

   This is `test/multiply_by_repeated_addition` written against Palow, and it
   is where the model's one real annotation cost shows up. Pulse computes the
   join for an `if` on its own, but it cannot invent a loop invariant, so the
   invariant has to restate the whole ownership frame: one existential ghost
   binder per live local, the points-to that binds it, and only then the
   proposition the C source wrote.

   The condition is read inside the `while` head rather than lifted out, for
   the same reason it is left inside an `assert`: Pulse A-normalises the call
   and `rewrites_to` states the resulting obligation in terms of the
   invariant's own binder. Nothing has to relate the loop's boolean to those
   binders -- Pulse re-runs the condition against the invariant and hands the
   body and the exit its truth and its falsity respectively.

   A loop makes the function divergent, since Palow does not translate the
   `decreases` measure that would keep it total.
   --------------------------------------------------------------------------- *)

divergent
fn multiply_by_repeated_addition (x y: U32.t)
  requires pure (U32.v x * U32.v y <= 4294967295)
  returns  r : U32.t
  ensures  pure (U32.v r == U32.v x * U32.v y)
{
  let loc_ctr = uint32_t_stack_alloc ();
  uint32_t_write_uninit loc_ctr 0ul;
  let loc_acc = uint32_t_stack_alloc ();
  uint32_t_write_uninit loc_acc 0ul;
  while (UInt32.lt (uint32_t_read loc_ctr) x)
    invariant exists* (vctr: U32.t) (vacc: U32.t).
      uint32_t_pts_to loc_ctr 1.0R vctr **
      uint32_t_pts_to loc_acc 1.0R vacc **
      pure (U32.v vctr <= U32.v x /\
            U32.v vacc == U32.v vctr * U32.v y)
  {
    uint32_t_write loc_ctr (UInt32.add (uint32_t_read loc_ctr) 1ul);
    uint32_t_write loc_acc (UInt32.add (uint32_t_read loc_acc) y);
  };
  let r = uint32_t_read loc_acc;
  uint32_t_forget loc_ctr;
  uint32_t_stack_free loc_ctr;
  uint32_t_forget loc_acc;
  uint32_t_stack_free loc_acc;
  r
}
