module Pulse.Lib.C.Palow.Unaligned
(* ---------------------------------------------------------------------------
   Unaligned access

   A field of a packed struct may sit at an address its type's alignment does
   not divide. Every typed points-to states that alignment, so such a field is
   held at the byte level instead: `elem_pts_to T_repr T_etype_ok a p x` is
   the bytes at `a` representing `x`, with nothing said about where `a` is,
   and `bytes_uninit T_etype_ok a n` is `n` bytes of storage the type admits.

   The operations on them add nothing to what is trusted. Each copies the bytes
   with `memcpy` to or from an aligned temporary on the stack and uses the
   type's ordinary aligned operation there. That is a model of what a compiler
   does for a packed member, not the code it emits: the Pulse is verified, and
   the C is what gets compiled.

   The per-type blocks are mechanically generated from one template.
   --------------------------------------------------------------------------- *)
#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Array
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.Float
open Pulse.Lib.C.Palow.CTypes
open Pulse.Lib.C.Palow.Machine
module ET = Pulse.Lib.C.Palow.Etype
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64

(* Storage for an unaligned field: `{t}_pts_to_uninit` less the alignment.
   It carries the effective-type index, and the condition the field's type
   puts on it, for the same reason the aligned predicate does -- a write has
   to be able to conclude that the bytes it filled may be read back at the
   type, and `memcpy` leaves the destination's index alone, so the index has
   to have been admissible before the write. Dropping it here would leave
   `{t}_write_uninit_u` with nothing to fold `elem_pts_to` from. *)
let bytes_uninit (eok: ET.etypes -> prop) ([@@@mkey] a: ptr) (n: nat) : slprop =
  exists* b e. mem_pts_to_at a 1.0R b e
               ** pure (len b == n /\ ET.elen e == n /\ eok e)

ghost fn bytes_claim_uninit (eok: ET.etypes -> prop) (a: ptr) (n: nat)
                            (#b: bytes) (#e: ET.etypes)
  requires mem_pts_to_at a 1.0R b e
  requires pure (len b == n /\ ET.elen e == n /\ eok e)
  ensures  bytes_uninit eok a n
{
  fold bytes_uninit eok a n;
}

ghost fn bytes_reveal_uninit (eok: ET.etypes -> prop) (a: ptr) (n: nat)
  requires bytes_uninit eok a n
  ensures  exists* b e. mem_pts_to_at a 1.0R b e
             ** pure (len b == n /\ ET.elen e == n /\ eok e)
{
  unfold bytes_uninit eok a n;
}

(* bool_t *)

ghost fn bool_t_forget_u (a: ptr) (#x: bool)
  requires elem_pts_to bool_t_repr bool_t_etype_ok a 1.0R x
  ensures  bytes_uninit bool_t_etype_ok a (SZ.v bool_t_sizeof)
{
  unfold elem_pts_to bool_t_repr bool_t_etype_ok a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  bool_t_repr_len x b;
  fold bytes_uninit bool_t_etype_ok a (SZ.v bool_t_sizeof);
}

fn bool_t_read_u (a: ptr) (#p: perm) (#x: erased bool)
  preserves elem_pts_to bool_t_repr bool_t_etype_ok a p x
  returns  y : bool
  ensures  rewrites_to y (reveal x)
{
  let t = bool_t_stack_alloc ();
  bool_t_reveal_uninit_at t;
  unfold elem_pts_to bool_t_repr bool_t_etype_ok a p x;
  with bs es. assert (mem_pts_to_at a p bs es);
  bool_t_repr_len x bs;
  memcpy t a bool_t_sizeof;
  bool_t_conceal t #1.0R #bs #_ #x;
  let y = bool_t_read t;
  bool_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  bool_t_repr_len x bt;
  bool_t_claim_uninit t;
  bool_t_stack_free t;
  fold elem_pts_to bool_t_repr bool_t_etype_ok a p x;
  y
}

fn bool_t_write_uninit_u (a: ptr) (y: bool)
  requires bytes_uninit bool_t_etype_ok a (SZ.v bool_t_sizeof)
  ensures  elem_pts_to bool_t_repr bool_t_etype_ok a 1.0R y
{
  let t = bool_t_stack_alloc ();
  bool_t_write_uninit t y;
  bool_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  bool_t_repr_len y bt;
  unfold bytes_uninit bool_t_etype_ok a (SZ.v bool_t_sizeof);
  with bd ed. assert (mem_pts_to_at a 1.0R bd ed);
  memcpy a t bool_t_sizeof;
  fold elem_pts_to bool_t_repr bool_t_etype_ok a 1.0R y;
  bool_t_claim_uninit t;
  bool_t_stack_free t;
}

fn bool_t_write_u (a: ptr) (y: bool) (#x: erased bool)
  requires elem_pts_to bool_t_repr bool_t_etype_ok a 1.0R x
  ensures  elem_pts_to bool_t_repr bool_t_etype_ok a 1.0R y
{
  bool_t_forget_u a;
  bool_t_write_uninit_u a y;
}

(* int8_t *)

ghost fn int8_t_forget_u (a: ptr) (#x: I8.t)
  requires elem_pts_to int8_t_repr int8_t_etype_ok a 1.0R x
  ensures  bytes_uninit int8_t_etype_ok a (SZ.v int8_t_sizeof)
{
  unfold elem_pts_to int8_t_repr int8_t_etype_ok a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  int8_t_repr_len x b;
  fold bytes_uninit int8_t_etype_ok a (SZ.v int8_t_sizeof);
}

fn int8_t_read_u (a: ptr) (#p: perm) (#x: erased I8.t)
  preserves elem_pts_to int8_t_repr int8_t_etype_ok a p x
  returns  y : I8.t
  ensures  rewrites_to y (reveal x)
{
  let t = int8_t_stack_alloc ();
  int8_t_reveal_uninit_at t;
  unfold elem_pts_to int8_t_repr int8_t_etype_ok a p x;
  with bs es. assert (mem_pts_to_at a p bs es);
  int8_t_repr_len x bs;
  memcpy t a int8_t_sizeof;
  int8_t_conceal t #1.0R #bs #_ #x;
  let y = int8_t_read t;
  int8_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  int8_t_repr_len x bt;
  int8_t_claim_uninit t;
  int8_t_stack_free t;
  fold elem_pts_to int8_t_repr int8_t_etype_ok a p x;
  y
}

fn int8_t_write_uninit_u (a: ptr) (y: I8.t)
  requires bytes_uninit int8_t_etype_ok a (SZ.v int8_t_sizeof)
  ensures  elem_pts_to int8_t_repr int8_t_etype_ok a 1.0R y
{
  let t = int8_t_stack_alloc ();
  int8_t_write_uninit t y;
  int8_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  int8_t_repr_len y bt;
  unfold bytes_uninit int8_t_etype_ok a (SZ.v int8_t_sizeof);
  with bd ed. assert (mem_pts_to_at a 1.0R bd ed);
  memcpy a t int8_t_sizeof;
  fold elem_pts_to int8_t_repr int8_t_etype_ok a 1.0R y;
  int8_t_claim_uninit t;
  int8_t_stack_free t;
}

fn int8_t_write_u (a: ptr) (y: I8.t) (#x: erased I8.t)
  requires elem_pts_to int8_t_repr int8_t_etype_ok a 1.0R x
  ensures  elem_pts_to int8_t_repr int8_t_etype_ok a 1.0R y
{
  int8_t_forget_u a;
  int8_t_write_uninit_u a y;
}

(* uint8_t *)

ghost fn uint8_t_forget_u (a: ptr) (#x: U8.t)
  requires elem_pts_to uint8_t_repr uint8_t_etype_ok a 1.0R x
  ensures  bytes_uninit uint8_t_etype_ok a (SZ.v uint8_t_sizeof)
{
  unfold elem_pts_to uint8_t_repr uint8_t_etype_ok a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  uint8_t_repr_len x b;
  fold bytes_uninit uint8_t_etype_ok a (SZ.v uint8_t_sizeof);
}

fn uint8_t_read_u (a: ptr) (#p: perm) (#x: erased U8.t)
  preserves elem_pts_to uint8_t_repr uint8_t_etype_ok a p x
  returns  y : U8.t
  ensures  rewrites_to y (reveal x)
{
  let t = uint8_t_stack_alloc ();
  uint8_t_reveal_uninit_at t;
  unfold elem_pts_to uint8_t_repr uint8_t_etype_ok a p x;
  with bs es. assert (mem_pts_to_at a p bs es);
  uint8_t_repr_len x bs;
  memcpy t a uint8_t_sizeof;
  uint8_t_conceal t #1.0R #bs #_ #x;
  let y = uint8_t_read t;
  uint8_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  uint8_t_repr_len x bt;
  uint8_t_claim_uninit t;
  uint8_t_stack_free t;
  fold elem_pts_to uint8_t_repr uint8_t_etype_ok a p x;
  y
}

fn uint8_t_write_uninit_u (a: ptr) (y: U8.t)
  requires bytes_uninit uint8_t_etype_ok a (SZ.v uint8_t_sizeof)
  ensures  elem_pts_to uint8_t_repr uint8_t_etype_ok a 1.0R y
{
  let t = uint8_t_stack_alloc ();
  uint8_t_write_uninit t y;
  uint8_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  uint8_t_repr_len y bt;
  unfold bytes_uninit uint8_t_etype_ok a (SZ.v uint8_t_sizeof);
  with bd ed. assert (mem_pts_to_at a 1.0R bd ed);
  memcpy a t uint8_t_sizeof;
  fold elem_pts_to uint8_t_repr uint8_t_etype_ok a 1.0R y;
  uint8_t_claim_uninit t;
  uint8_t_stack_free t;
}

fn uint8_t_write_u (a: ptr) (y: U8.t) (#x: erased U8.t)
  requires elem_pts_to uint8_t_repr uint8_t_etype_ok a 1.0R x
  ensures  elem_pts_to uint8_t_repr uint8_t_etype_ok a 1.0R y
{
  uint8_t_forget_u a;
  uint8_t_write_uninit_u a y;
}

(* int16_t *)

ghost fn int16_t_forget_u (a: ptr) (#x: I16.t)
  requires elem_pts_to int16_t_repr int16_t_etype_ok a 1.0R x
  ensures  bytes_uninit int16_t_etype_ok a (SZ.v int16_t_sizeof)
{
  unfold elem_pts_to int16_t_repr int16_t_etype_ok a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  int16_t_repr_len x b;
  fold bytes_uninit int16_t_etype_ok a (SZ.v int16_t_sizeof);
}

fn int16_t_read_u (a: ptr) (#p: perm) (#x: erased I16.t)
  preserves elem_pts_to int16_t_repr int16_t_etype_ok a p x
  returns  y : I16.t
  ensures  rewrites_to y (reveal x)
{
  let t = int16_t_stack_alloc ();
  int16_t_reveal_uninit_at t;
  unfold elem_pts_to int16_t_repr int16_t_etype_ok a p x;
  with bs es. assert (mem_pts_to_at a p bs es);
  int16_t_repr_len x bs;
  memcpy t a int16_t_sizeof;
  int16_t_conceal t #1.0R #bs #_ #x;
  let y = int16_t_read t;
  int16_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  int16_t_repr_len x bt;
  int16_t_claim_uninit t;
  int16_t_stack_free t;
  fold elem_pts_to int16_t_repr int16_t_etype_ok a p x;
  y
}

fn int16_t_write_uninit_u (a: ptr) (y: I16.t)
  requires bytes_uninit int16_t_etype_ok a (SZ.v int16_t_sizeof)
  ensures  elem_pts_to int16_t_repr int16_t_etype_ok a 1.0R y
{
  let t = int16_t_stack_alloc ();
  int16_t_write_uninit t y;
  int16_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  int16_t_repr_len y bt;
  unfold bytes_uninit int16_t_etype_ok a (SZ.v int16_t_sizeof);
  with bd ed. assert (mem_pts_to_at a 1.0R bd ed);
  memcpy a t int16_t_sizeof;
  fold elem_pts_to int16_t_repr int16_t_etype_ok a 1.0R y;
  int16_t_claim_uninit t;
  int16_t_stack_free t;
}

fn int16_t_write_u (a: ptr) (y: I16.t) (#x: erased I16.t)
  requires elem_pts_to int16_t_repr int16_t_etype_ok a 1.0R x
  ensures  elem_pts_to int16_t_repr int16_t_etype_ok a 1.0R y
{
  int16_t_forget_u a;
  int16_t_write_uninit_u a y;
}

(* uint16_t *)

ghost fn uint16_t_forget_u (a: ptr) (#x: U16.t)
  requires elem_pts_to uint16_t_repr uint16_t_etype_ok a 1.0R x
  ensures  bytes_uninit uint16_t_etype_ok a (SZ.v uint16_t_sizeof)
{
  unfold elem_pts_to uint16_t_repr uint16_t_etype_ok a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  uint16_t_repr_len x b;
  fold bytes_uninit uint16_t_etype_ok a (SZ.v uint16_t_sizeof);
}

fn uint16_t_read_u (a: ptr) (#p: perm) (#x: erased U16.t)
  preserves elem_pts_to uint16_t_repr uint16_t_etype_ok a p x
  returns  y : U16.t
  ensures  rewrites_to y (reveal x)
{
  let t = uint16_t_stack_alloc ();
  uint16_t_reveal_uninit_at t;
  unfold elem_pts_to uint16_t_repr uint16_t_etype_ok a p x;
  with bs es. assert (mem_pts_to_at a p bs es);
  uint16_t_repr_len x bs;
  memcpy t a uint16_t_sizeof;
  uint16_t_conceal t #1.0R #bs #_ #x;
  let y = uint16_t_read t;
  uint16_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  uint16_t_repr_len x bt;
  uint16_t_claim_uninit t;
  uint16_t_stack_free t;
  fold elem_pts_to uint16_t_repr uint16_t_etype_ok a p x;
  y
}

fn uint16_t_write_uninit_u (a: ptr) (y: U16.t)
  requires bytes_uninit uint16_t_etype_ok a (SZ.v uint16_t_sizeof)
  ensures  elem_pts_to uint16_t_repr uint16_t_etype_ok a 1.0R y
{
  let t = uint16_t_stack_alloc ();
  uint16_t_write_uninit t y;
  uint16_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  uint16_t_repr_len y bt;
  unfold bytes_uninit uint16_t_etype_ok a (SZ.v uint16_t_sizeof);
  with bd ed. assert (mem_pts_to_at a 1.0R bd ed);
  memcpy a t uint16_t_sizeof;
  fold elem_pts_to uint16_t_repr uint16_t_etype_ok a 1.0R y;
  uint16_t_claim_uninit t;
  uint16_t_stack_free t;
}

fn uint16_t_write_u (a: ptr) (y: U16.t) (#x: erased U16.t)
  requires elem_pts_to uint16_t_repr uint16_t_etype_ok a 1.0R x
  ensures  elem_pts_to uint16_t_repr uint16_t_etype_ok a 1.0R y
{
  uint16_t_forget_u a;
  uint16_t_write_uninit_u a y;
}

(* int32_t *)

ghost fn int32_t_forget_u (a: ptr) (#x: I32.t)
  requires elem_pts_to int32_t_repr int32_t_etype_ok a 1.0R x
  ensures  bytes_uninit int32_t_etype_ok a (SZ.v int32_t_sizeof)
{
  unfold elem_pts_to int32_t_repr int32_t_etype_ok a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  int32_t_repr_len x b;
  fold bytes_uninit int32_t_etype_ok a (SZ.v int32_t_sizeof);
}

fn int32_t_read_u (a: ptr) (#p: perm) (#x: erased I32.t)
  preserves elem_pts_to int32_t_repr int32_t_etype_ok a p x
  returns  y : I32.t
  ensures  rewrites_to y (reveal x)
{
  let t = int32_t_stack_alloc ();
  int32_t_reveal_uninit_at t;
  unfold elem_pts_to int32_t_repr int32_t_etype_ok a p x;
  with bs es. assert (mem_pts_to_at a p bs es);
  int32_t_repr_len x bs;
  memcpy t a int32_t_sizeof;
  int32_t_conceal t #1.0R #bs #_ #x;
  let y = int32_t_read t;
  int32_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  int32_t_repr_len x bt;
  int32_t_claim_uninit t;
  int32_t_stack_free t;
  fold elem_pts_to int32_t_repr int32_t_etype_ok a p x;
  y
}

fn int32_t_write_uninit_u (a: ptr) (y: I32.t)
  requires bytes_uninit int32_t_etype_ok a (SZ.v int32_t_sizeof)
  ensures  elem_pts_to int32_t_repr int32_t_etype_ok a 1.0R y
{
  let t = int32_t_stack_alloc ();
  int32_t_write_uninit t y;
  int32_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  int32_t_repr_len y bt;
  unfold bytes_uninit int32_t_etype_ok a (SZ.v int32_t_sizeof);
  with bd ed. assert (mem_pts_to_at a 1.0R bd ed);
  memcpy a t int32_t_sizeof;
  fold elem_pts_to int32_t_repr int32_t_etype_ok a 1.0R y;
  int32_t_claim_uninit t;
  int32_t_stack_free t;
}

fn int32_t_write_u (a: ptr) (y: I32.t) (#x: erased I32.t)
  requires elem_pts_to int32_t_repr int32_t_etype_ok a 1.0R x
  ensures  elem_pts_to int32_t_repr int32_t_etype_ok a 1.0R y
{
  int32_t_forget_u a;
  int32_t_write_uninit_u a y;
}

(* uint32_t *)

ghost fn uint32_t_forget_u (a: ptr) (#x: U32.t)
  requires elem_pts_to uint32_t_repr uint32_t_etype_ok a 1.0R x
  ensures  bytes_uninit uint32_t_etype_ok a (SZ.v uint32_t_sizeof)
{
  unfold elem_pts_to uint32_t_repr uint32_t_etype_ok a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  uint32_t_repr_len x b;
  fold bytes_uninit uint32_t_etype_ok a (SZ.v uint32_t_sizeof);
}

fn uint32_t_read_u (a: ptr) (#p: perm) (#x: erased U32.t)
  preserves elem_pts_to uint32_t_repr uint32_t_etype_ok a p x
  returns  y : U32.t
  ensures  rewrites_to y (reveal x)
{
  let t = uint32_t_stack_alloc ();
  uint32_t_reveal_uninit_at t;
  unfold elem_pts_to uint32_t_repr uint32_t_etype_ok a p x;
  with bs es. assert (mem_pts_to_at a p bs es);
  uint32_t_repr_len x bs;
  memcpy t a uint32_t_sizeof;
  uint32_t_conceal t #1.0R #bs #_ #x;
  let y = uint32_t_read t;
  uint32_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  uint32_t_repr_len x bt;
  uint32_t_claim_uninit t;
  uint32_t_stack_free t;
  fold elem_pts_to uint32_t_repr uint32_t_etype_ok a p x;
  y
}

fn uint32_t_write_uninit_u (a: ptr) (y: U32.t)
  requires bytes_uninit uint32_t_etype_ok a (SZ.v uint32_t_sizeof)
  ensures  elem_pts_to uint32_t_repr uint32_t_etype_ok a 1.0R y
{
  let t = uint32_t_stack_alloc ();
  uint32_t_write_uninit t y;
  uint32_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  uint32_t_repr_len y bt;
  unfold bytes_uninit uint32_t_etype_ok a (SZ.v uint32_t_sizeof);
  with bd ed. assert (mem_pts_to_at a 1.0R bd ed);
  memcpy a t uint32_t_sizeof;
  fold elem_pts_to uint32_t_repr uint32_t_etype_ok a 1.0R y;
  uint32_t_claim_uninit t;
  uint32_t_stack_free t;
}

fn uint32_t_write_u (a: ptr) (y: U32.t) (#x: erased U32.t)
  requires elem_pts_to uint32_t_repr uint32_t_etype_ok a 1.0R x
  ensures  elem_pts_to uint32_t_repr uint32_t_etype_ok a 1.0R y
{
  uint32_t_forget_u a;
  uint32_t_write_uninit_u a y;
}

(* int64_t *)

ghost fn int64_t_forget_u (a: ptr) (#x: I64.t)
  requires elem_pts_to int64_t_repr int64_t_etype_ok a 1.0R x
  ensures  bytes_uninit int64_t_etype_ok a (SZ.v int64_t_sizeof)
{
  unfold elem_pts_to int64_t_repr int64_t_etype_ok a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  int64_t_repr_len x b;
  fold bytes_uninit int64_t_etype_ok a (SZ.v int64_t_sizeof);
}

fn int64_t_read_u (a: ptr) (#p: perm) (#x: erased I64.t)
  preserves elem_pts_to int64_t_repr int64_t_etype_ok a p x
  returns  y : I64.t
  ensures  rewrites_to y (reveal x)
{
  let t = int64_t_stack_alloc ();
  int64_t_reveal_uninit_at t;
  unfold elem_pts_to int64_t_repr int64_t_etype_ok a p x;
  with bs es. assert (mem_pts_to_at a p bs es);
  int64_t_repr_len x bs;
  memcpy t a int64_t_sizeof;
  int64_t_conceal t #1.0R #bs #_ #x;
  let y = int64_t_read t;
  int64_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  int64_t_repr_len x bt;
  int64_t_claim_uninit t;
  int64_t_stack_free t;
  fold elem_pts_to int64_t_repr int64_t_etype_ok a p x;
  y
}

fn int64_t_write_uninit_u (a: ptr) (y: I64.t)
  requires bytes_uninit int64_t_etype_ok a (SZ.v int64_t_sizeof)
  ensures  elem_pts_to int64_t_repr int64_t_etype_ok a 1.0R y
{
  let t = int64_t_stack_alloc ();
  int64_t_write_uninit t y;
  int64_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  int64_t_repr_len y bt;
  unfold bytes_uninit int64_t_etype_ok a (SZ.v int64_t_sizeof);
  with bd ed. assert (mem_pts_to_at a 1.0R bd ed);
  memcpy a t int64_t_sizeof;
  fold elem_pts_to int64_t_repr int64_t_etype_ok a 1.0R y;
  int64_t_claim_uninit t;
  int64_t_stack_free t;
}

fn int64_t_write_u (a: ptr) (y: I64.t) (#x: erased I64.t)
  requires elem_pts_to int64_t_repr int64_t_etype_ok a 1.0R x
  ensures  elem_pts_to int64_t_repr int64_t_etype_ok a 1.0R y
{
  int64_t_forget_u a;
  int64_t_write_uninit_u a y;
}

(* uint64_t *)

ghost fn uint64_t_forget_u (a: ptr) (#x: U64.t)
  requires elem_pts_to uint64_t_repr uint64_t_etype_ok a 1.0R x
  ensures  bytes_uninit uint64_t_etype_ok a (SZ.v uint64_t_sizeof)
{
  unfold elem_pts_to uint64_t_repr uint64_t_etype_ok a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  uint64_t_repr_len x b;
  fold bytes_uninit uint64_t_etype_ok a (SZ.v uint64_t_sizeof);
}

fn uint64_t_read_u (a: ptr) (#p: perm) (#x: erased U64.t)
  preserves elem_pts_to uint64_t_repr uint64_t_etype_ok a p x
  returns  y : U64.t
  ensures  rewrites_to y (reveal x)
{
  let t = uint64_t_stack_alloc ();
  uint64_t_reveal_uninit_at t;
  unfold elem_pts_to uint64_t_repr uint64_t_etype_ok a p x;
  with bs es. assert (mem_pts_to_at a p bs es);
  uint64_t_repr_len x bs;
  memcpy t a uint64_t_sizeof;
  uint64_t_conceal t #1.0R #bs #_ #x;
  let y = uint64_t_read t;
  uint64_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  uint64_t_repr_len x bt;
  uint64_t_claim_uninit t;
  uint64_t_stack_free t;
  fold elem_pts_to uint64_t_repr uint64_t_etype_ok a p x;
  y
}

fn uint64_t_write_uninit_u (a: ptr) (y: U64.t)
  requires bytes_uninit uint64_t_etype_ok a (SZ.v uint64_t_sizeof)
  ensures  elem_pts_to uint64_t_repr uint64_t_etype_ok a 1.0R y
{
  let t = uint64_t_stack_alloc ();
  uint64_t_write_uninit t y;
  uint64_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  uint64_t_repr_len y bt;
  unfold bytes_uninit uint64_t_etype_ok a (SZ.v uint64_t_sizeof);
  with bd ed. assert (mem_pts_to_at a 1.0R bd ed);
  memcpy a t uint64_t_sizeof;
  fold elem_pts_to uint64_t_repr uint64_t_etype_ok a 1.0R y;
  uint64_t_claim_uninit t;
  uint64_t_stack_free t;
}

fn uint64_t_write_u (a: ptr) (y: U64.t) (#x: erased U64.t)
  requires elem_pts_to uint64_t_repr uint64_t_etype_ok a 1.0R x
  ensures  elem_pts_to uint64_t_repr uint64_t_etype_ok a 1.0R y
{
  uint64_t_forget_u a;
  uint64_t_write_uninit_u a y;
}

(* size_t *)

ghost fn size_t_forget_u (a: ptr) (#x: SZ.t)
  requires elem_pts_to size_t_repr size_t_etype_ok a 1.0R x
  ensures  bytes_uninit size_t_etype_ok a (SZ.v size_t_sizeof)
{
  unfold elem_pts_to size_t_repr size_t_etype_ok a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  size_t_repr_len x b;
  fold bytes_uninit size_t_etype_ok a (SZ.v size_t_sizeof);
}

fn size_t_read_u (a: ptr) (#p: perm) (#x: erased SZ.t)
  preserves elem_pts_to size_t_repr size_t_etype_ok a p x
  returns  y : SZ.t
  ensures  rewrites_to y (reveal x)
{
  let t = size_t_stack_alloc ();
  size_t_reveal_uninit_at t;
  unfold elem_pts_to size_t_repr size_t_etype_ok a p x;
  with bs es. assert (mem_pts_to_at a p bs es);
  size_t_repr_len x bs;
  memcpy t a size_t_sizeof;
  size_t_conceal t #1.0R #bs #_ #x;
  let y = size_t_read t;
  size_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  size_t_repr_len x bt;
  size_t_claim_uninit t;
  size_t_stack_free t;
  fold elem_pts_to size_t_repr size_t_etype_ok a p x;
  y
}

fn size_t_write_uninit_u (a: ptr) (y: SZ.t)
  requires bytes_uninit size_t_etype_ok a (SZ.v size_t_sizeof)
  ensures  elem_pts_to size_t_repr size_t_etype_ok a 1.0R y
{
  let t = size_t_stack_alloc ();
  size_t_write_uninit t y;
  size_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  size_t_repr_len y bt;
  unfold bytes_uninit size_t_etype_ok a (SZ.v size_t_sizeof);
  with bd ed. assert (mem_pts_to_at a 1.0R bd ed);
  memcpy a t size_t_sizeof;
  fold elem_pts_to size_t_repr size_t_etype_ok a 1.0R y;
  size_t_claim_uninit t;
  size_t_stack_free t;
}

fn size_t_write_u (a: ptr) (y: SZ.t) (#x: erased SZ.t)
  requires elem_pts_to size_t_repr size_t_etype_ok a 1.0R x
  ensures  elem_pts_to size_t_repr size_t_etype_ok a 1.0R y
{
  size_t_forget_u a;
  size_t_write_uninit_u a y;
}

(* float32_t *)

ghost fn float32_t_forget_u (a: ptr) (#x: float32)
  requires elem_pts_to float32_t_repr float32_t_etype_ok a 1.0R x
  ensures  bytes_uninit float32_t_etype_ok a (SZ.v float32_t_sizeof)
{
  unfold elem_pts_to float32_t_repr float32_t_etype_ok a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  float32_t_repr_len x b;
  fold bytes_uninit float32_t_etype_ok a (SZ.v float32_t_sizeof);
}

fn float32_t_read_u (a: ptr) (#p: perm) (#x: erased float32)
  preserves elem_pts_to float32_t_repr float32_t_etype_ok a p x
  returns  y : float32
  ensures  rewrites_to y (reveal x)
{
  let t = float32_t_stack_alloc ();
  float32_t_reveal_uninit_at t;
  unfold elem_pts_to float32_t_repr float32_t_etype_ok a p x;
  with bs es. assert (mem_pts_to_at a p bs es);
  float32_t_repr_len x bs;
  memcpy t a float32_t_sizeof;
  float32_t_conceal t #1.0R #bs #_ #x;
  let y = float32_t_read t;
  float32_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  float32_t_repr_len x bt;
  float32_t_claim_uninit t;
  float32_t_stack_free t;
  fold elem_pts_to float32_t_repr float32_t_etype_ok a p x;
  y
}

fn float32_t_write_uninit_u (a: ptr) (y: float32)
  requires bytes_uninit float32_t_etype_ok a (SZ.v float32_t_sizeof)
  ensures  elem_pts_to float32_t_repr float32_t_etype_ok a 1.0R y
{
  let t = float32_t_stack_alloc ();
  float32_t_write_uninit t y;
  float32_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  float32_t_repr_len y bt;
  unfold bytes_uninit float32_t_etype_ok a (SZ.v float32_t_sizeof);
  with bd ed. assert (mem_pts_to_at a 1.0R bd ed);
  memcpy a t float32_t_sizeof;
  fold elem_pts_to float32_t_repr float32_t_etype_ok a 1.0R y;
  float32_t_claim_uninit t;
  float32_t_stack_free t;
}

fn float32_t_write_u (a: ptr) (y: float32) (#x: erased float32)
  requires elem_pts_to float32_t_repr float32_t_etype_ok a 1.0R x
  ensures  elem_pts_to float32_t_repr float32_t_etype_ok a 1.0R y
{
  float32_t_forget_u a;
  float32_t_write_uninit_u a y;
}

(* float64_t *)

ghost fn float64_t_forget_u (a: ptr) (#x: float64)
  requires elem_pts_to float64_t_repr float64_t_etype_ok a 1.0R x
  ensures  bytes_uninit float64_t_etype_ok a (SZ.v float64_t_sizeof)
{
  unfold elem_pts_to float64_t_repr float64_t_etype_ok a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  float64_t_repr_len x b;
  fold bytes_uninit float64_t_etype_ok a (SZ.v float64_t_sizeof);
}

fn float64_t_read_u (a: ptr) (#p: perm) (#x: erased float64)
  preserves elem_pts_to float64_t_repr float64_t_etype_ok a p x
  returns  y : float64
  ensures  rewrites_to y (reveal x)
{
  let t = float64_t_stack_alloc ();
  float64_t_reveal_uninit_at t;
  unfold elem_pts_to float64_t_repr float64_t_etype_ok a p x;
  with bs es. assert (mem_pts_to_at a p bs es);
  float64_t_repr_len x bs;
  memcpy t a float64_t_sizeof;
  float64_t_conceal t #1.0R #bs #_ #x;
  let y = float64_t_read t;
  float64_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  float64_t_repr_len x bt;
  float64_t_claim_uninit t;
  float64_t_stack_free t;
  fold elem_pts_to float64_t_repr float64_t_etype_ok a p x;
  y
}

fn float64_t_write_uninit_u (a: ptr) (y: float64)
  requires bytes_uninit float64_t_etype_ok a (SZ.v float64_t_sizeof)
  ensures  elem_pts_to float64_t_repr float64_t_etype_ok a 1.0R y
{
  let t = float64_t_stack_alloc ();
  float64_t_write_uninit t y;
  float64_t_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  float64_t_repr_len y bt;
  unfold bytes_uninit float64_t_etype_ok a (SZ.v float64_t_sizeof);
  with bd ed. assert (mem_pts_to_at a 1.0R bd ed);
  memcpy a t float64_t_sizeof;
  fold elem_pts_to float64_t_repr float64_t_etype_ok a 1.0R y;
  float64_t_claim_uninit t;
  float64_t_stack_free t;
}

fn float64_t_write_u (a: ptr) (y: float64) (#x: erased float64)
  requires elem_pts_to float64_t_repr float64_t_etype_ok a 1.0R x
  ensures  elem_pts_to float64_t_repr float64_t_etype_ok a 1.0R y
{
  float64_t_forget_u a;
  float64_t_write_uninit_u a y;
}

(* ptr *)

ghost fn ptr_forget_u (a: ptr) (#x: ptr)
  requires elem_pts_to ptr_repr ptr_etype_ok a 1.0R x
  ensures  bytes_uninit ptr_etype_ok a (SZ.v ptr_sizeof)
{
  unfold elem_pts_to ptr_repr ptr_etype_ok a 1.0R x;
  with b e. assert (mem_pts_to_at a 1.0R b e);
  ptr_repr_len x b;
  fold bytes_uninit ptr_etype_ok a (SZ.v ptr_sizeof);
}

fn ptr_read_u (a: ptr) (#p: perm) (#x: erased ptr)
  preserves elem_pts_to ptr_repr ptr_etype_ok a p x
  returns  y : ptr
  ensures  rewrites_to y (reveal x)
{
  let t = ptr_stack_alloc ();
  ptr_reveal_uninit_at t;
  unfold elem_pts_to ptr_repr ptr_etype_ok a p x;
  with bs es. assert (mem_pts_to_at a p bs es);
  ptr_repr_len x bs;
  memcpy t a ptr_sizeof;
  ptr_conceal t #1.0R #bs #_ #x;
  let y = ptr_read t;
  ptr_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  ptr_repr_len x bt;
  ptr_claim_uninit t;
  ptr_stack_free t;
  fold elem_pts_to ptr_repr ptr_etype_ok a p x;
  y
}

fn ptr_write_uninit_u (a: ptr) (y: ptr)
  requires bytes_uninit ptr_etype_ok a (SZ.v ptr_sizeof)
  ensures  elem_pts_to ptr_repr ptr_etype_ok a 1.0R y
{
  let t = ptr_stack_alloc ();
  ptr_write_uninit t y;
  ptr_reveal t;
  with bt et. assert (mem_pts_to_at t 1.0R bt et);
  ptr_repr_len y bt;
  unfold bytes_uninit ptr_etype_ok a (SZ.v ptr_sizeof);
  with bd ed. assert (mem_pts_to_at a 1.0R bd ed);
  memcpy a t ptr_sizeof;
  fold elem_pts_to ptr_repr ptr_etype_ok a 1.0R y;
  ptr_claim_uninit t;
  ptr_stack_free t;
}

fn ptr_write_u (a: ptr) (y: ptr) (#x: erased ptr)
  requires elem_pts_to ptr_repr ptr_etype_ok a 1.0R x
  ensures  elem_pts_to ptr_repr ptr_etype_ok a 1.0R y
{
  ptr_forget_u a;
  ptr_write_uninit_u a y;
}

