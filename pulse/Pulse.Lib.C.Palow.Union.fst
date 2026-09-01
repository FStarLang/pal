module Pulse.Lib.C.Palow.Union

(* ---------------------------------------------------------------------------
   Unions, and the type-punning acceptance test from `palow.md`:

     union { int x; struct { int y; int z; }; } a;
     a.x = 10;
     int b = a.y;
     _assert(b == 10);

   This program is legal C and is exactly what today's model cannot express:
   `a.x` and `a.y` are different F* fields of different F* types, so there is
   no way to say that storing through one is observable through the other.
   Palow has one answer for both: they name the *same bytes*, and reading them
   back at either type goes through the same `mem_pts_to`.

   Modelled here with `uint32_t` in place of `int`, since that is the scalar
   type `Pulse.Lib.C.Palow.Scalar` provides.

     union U { uint32_t x; struct T t; };   // sizeof 8, alignof 4

   The union's representation is *not* injective, and that is the point: a byte
   range that represents `U_x v` also represents `U_t {y = v; z = w}` for
   whatever `w` the trailing bytes happen to encode. Palow does not need the
   `*_pts_to` predicates to be injective anywhere, which is what makes this
   expressible at all.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow.Encoding
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.Aggregate
open Pulse.Lib.C.Palow.Machine

module SZ = FStar.SizeT
module Seq = FStar.Seq
module U32 = FStar.UInt32

noeq type union_U =
  | U_x : U32.t -> union_U
  | U_t : struct_T -> union_U

let union_U_sizeof : SZ.t = 8sz
let union_U_alignof : SZ.t = 4sz

(* A union's `*_repr` relates a value to the bytes of whichever member it
   holds. Members shorter than the union leave the remaining bytes
   unconstrained -- `a.x = 10` says nothing about bytes 4..8, matching C. *)
let union_U_repr (u: union_U) (b: bytes) : prop =
  len b == SZ.v union_U_sizeof /\
  (len b == SZ.v union_U_sizeof ==>
     (match u with
      | U_x v -> uint32_t_repr v (slice b 0 4)
      | U_t t -> struct_T_repr t b))

let union_U_pts_to ([@@@mkey] a: ptr) (p: perm) (u: union_U) : slprop =
  exists* b. mem_pts_to a p b ** pure (union_U_repr u b)

(* Ownership of the bytes past the end of the `x` member. The `x` view hands
   these back separately so that the union can be reassembled, and so that a
   client cannot silently forget that they exist. *)
let union_U_x_rest ([@@@mkey] a: ptr) (p: perm) : slprop =
  exists* b. mem_pts_to (a +! 4sz) p b ** pure (len b == 4)

(* ---------------------------------------------------------------------------
   Member views

   Each member view is `mem_split` at the member's extent followed by a fold at
   the member's type. Note that both members start at offset 0, so the `x` view
   and the `t.y` view produce the *same* resource at the *same* address -- that
   equality is the whole content of the pun.
   --------------------------------------------------------------------------- *)

ghost fn union_U_split_x (a: ptr) (#p: perm) (#v: U32.t)
  requires union_U_pts_to a p (U_x v)
  ensures  uint32_t_pts_to a p v
  ensures  union_U_x_rest a p
{
  unfold union_U_pts_to a p (U_x v);
  with b. assert (mem_pts_to a p b ** pure (union_U_repr (U_x v) b));
  mem_split a 4sz;
  Seq.lemma_eq_intro (slice b 0 4) (encode 4 None (U32.v v));
  fold uint32_t_pts_to a p v;
  fold union_U_x_rest a p;
}

ghost fn union_U_join_x (a: ptr) (#p: perm) (#v: U32.t)
  requires uint32_t_pts_to a p v
  requires union_U_x_rest a p
  ensures  union_U_pts_to a p (U_x v)
{
  unfold uint32_t_pts_to a p v;
  unfold union_U_x_rest a p;
  with rest. assert (mem_pts_to (a +! 4sz) p rest);
  mem_join a #p #(encode 4 None (U32.v v)) #rest 4sz;
  append_slice_left (encode 4 None (U32.v v)) rest;
  fold union_U_pts_to a p (U_x v);
}

ghost fn union_U_split_t (a: ptr) (#p: perm) (#t: struct_T)
  requires union_U_pts_to a p (U_t t)
  ensures  struct_T_pts_to a p t
{
  unfold union_U_pts_to a p (U_t t);
  fold struct_T_pts_to a p t;
}

ghost fn union_U_join_t (a: ptr) (#p: perm) (#t: struct_T)
  requires struct_T_pts_to a p t
  ensures  union_U_pts_to a p (U_t t)
{
  unfold struct_T_pts_to a p t;
  fold union_U_pts_to a p (U_t t);
}

(* ---------------------------------------------------------------------------
   The pun, as a pure fact about representations

   If the bytes represent `U_x v` and their tail happens to represent some `w`,
   then they equally represent `U_t {y = v; z = w}`. This is where the
   non-injectivity of `union_U_repr` is used, and it is the reason `a.y` reads
   back what `a.x` wrote.
   --------------------------------------------------------------------------- *)

let union_U_pun (v w: U32.t) (b: bytes)
  : Lemma (requires union_U_repr (U_x v) b /\ uint32_t_repr w (slice b 4 8))
          (ensures  union_U_repr (U_t ({ y = v; z = w })) b)
  = ()

(* ---------------------------------------------------------------------------
   Reading a member is a *field*-level access

   `a.y` needs the bytes of `y` only; `a.z` may still be uninitialized. That is
   why the program below may read `a.y` immediately after `a.x = 10` even
   though nothing has ever written bytes 4..8, and it is what field-level
   ownership buys over object-level ownership. Since `y` sits at offset 0 of
   the struct member and `x` at offset 0 of the union, the resource for `a.x`
   and the resource for `a.y` are literally the same slprop.
   --------------------------------------------------------------------------- *)

ghost fn union_U_focus_t_y (a: ptr) (#p: perm) (#v: U32.t)
  requires uint32_t_pts_to a p v
  ensures  uint32_t_pts_to (a +! struct_T_offsetof_y) p v
{
  rewrite (uint32_t_pts_to a p v)
       as (uint32_t_pts_to (a +! struct_T_offsetof_y) p v);
}

ghost fn union_U_unfocus_t_y (a: ptr) (#p: perm) (#v: U32.t)
  requires uint32_t_pts_to (a +! struct_T_offsetof_y) p v
  ensures  uint32_t_pts_to a p v
{
  rewrite (uint32_t_pts_to (a +! struct_T_offsetof_y) p v)
       as (uint32_t_pts_to a p v);
}

(* ---------------------------------------------------------------------------
   Acceptance test 2, as an executable Pulse program.

   `a` starts out as arbitrary union storage. We store through `.x` and read
   back through `.t.y`, and the postcondition records that the value survives.
   No axiom is involved: the store and the load are the ordinary machine
   operations, and everything between them is `mem_split` / `mem_join`.
   --------------------------------------------------------------------------- *)

fn union_pun_test (a: ptr) (#u0: erased union_U)
  requires union_U_pts_to a 1.0R u0
  returns  b: U32.t
  ensures  union_U_pts_to a 1.0R (U_x 10ul)
  ensures  pure (b == 10ul)
{
  (* a.x = 10; -- the store only needs the first four bytes, whatever they
     previously held and whichever member the union was in. *)
  unfold union_U_pts_to a 1.0R u0;
  with b0. assert (mem_pts_to a 1.0R b0 ** pure (union_U_repr u0 b0));
  mem_split a 4sz;
  fold uint32_t_pts_to_uninit a;
  uint32_t_write_uninit a 10ul;
  fold union_U_x_rest a 1.0R;

  (* int b = a.y; *)
  union_U_focus_t_y a;
  let r = uint32_t_read (a +! struct_T_offsetof_y);
  union_U_unfocus_t_y a;

  union_U_join_x a;
  r
}

(* The same program written through the struct member view instead: here the
   union really is inhabited by `U_t`, so `a.z` is readable too, and the write
   to `a.x` is visible as a change to `a.y` while leaving `a.z` alone. *)
fn union_pun_test_struct (a: ptr) (#t0: erased struct_T)
  requires union_U_pts_to a 1.0R (U_t t0)
  returns  b: U32.t
  ensures  union_U_pts_to a 1.0R (U_t ({ y = 10ul; z = (reveal t0).z }))
  ensures  pure (b == 10ul)
{
  union_U_split_t a;
  struct_T_split a;

  (* a.x = 10 *)
  uint32_t_write a 10ul;

  (* int b = a.y *)
  union_U_focus_t_y a;
  let r = uint32_t_read (a +! struct_T_offsetof_y);
  union_U_unfocus_t_y a;

  struct_T_join a #1.0R #({ y = 10ul; z = (reveal t0).z });
  union_U_join_t a;
  r
}
