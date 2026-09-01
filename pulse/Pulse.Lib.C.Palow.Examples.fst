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

module I32 = FStar.Int32

(* test/swap/swap.c:

     void swap(int *x, int *y)
       _ensures(*y == _old(*x) && *x == _old(*y))
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
  returns   r : I32.t
  requires  pure (I32.fits (I32.v a + I32.v b))
  ensures   pure (I32.v r == I32.v a + I32.v b)
{
  let va = int32_t_read x;
  let vb = int32_t_read y;
  I32.add va vb
}
