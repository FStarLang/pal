module Loan
#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes
open Pulse.Lib.C.Palow.Array
module SizeT = FStar.SizeT
open Struct_trailer
open Struct_packet

(* All of `*a` but `buffer`, with `trailer` at `q`. The name ends in
   `struct_packet_hole_...`, which is what makes PAL treat an assertion of it
   as a field loan. *)
let struct_packet_hole_lent (a: ptr) (q: perm) (x: struct_packet) : slprop =
  int32_t_pts_to (a +! struct_packet_offsetof_header) 1.0R (x).fld_header **
  struct_trailer_pts_to (a +! struct_packet_offsetof_trailer) q (x).fld_trailer **
  struct_packet_padding a 1.0R

(* At `q = 1.0R` it is the generated hole: the two cannot drift apart. *)
let hole_lent_full (a: ptr) (x: struct_packet)
  : squash (struct_packet_hole_lent a 1.0R x == struct_packet_hole_buffer a 1.0R x)
  = ()

ghost fn lend_buffer (a: ptr) (#x: erased struct_packet)
  requires struct_packet_pts_to a 1.0R x
  ensures struct_packet_hole_lent a 1.0R x
  ensures array_pts_to uint8_t_repr 1 (SizeT.v uint8_t_alignof) (a +! struct_packet_offsetof_buffer) 1.0R x.fld_buffer
{
  struct_packet_focus_buffer a;
  unfold struct_packet_hole_buffer a 1.0R x;
  fold struct_packet_hole_lent a 1.0R x;
}

ghost fn return_buffer (a: ptr) (#x: erased struct_packet)
  requires struct_packet_hole_lent a 1.0R x
  requires array_pts_to uint8_t_repr 1 (SizeT.v uint8_t_alignof) (a +! struct_packet_offsetof_buffer) 1.0R x.fld_buffer
  ensures struct_packet_pts_to a 1.0R x
{
  unfold struct_packet_hole_lent a 1.0R x;
  fold struct_packet_hole_buffer a 1.0R x;
  struct_packet_unfocus_read_buffer a;
}
