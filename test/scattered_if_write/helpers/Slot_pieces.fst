module Slot_pieces
#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes
open Pulse.Lib.C.Palow.Machine
open Struct_holder

(* A holder as a gate lends it: its fields one points-to each, behind one
   predicate. *)
unfold let parts (h: ptr) : slprop =
  struct_holder_padding h 1.0R **
  (exists* (p: ptr). ptr_pts_to (h +! struct_holder_offsetof_slot) 1.0R p) **
  (exists* (n: FStar.Int32.t). int32_t_pts_to (h +! struct_holder_offsetof_count) 1.0R n)

let pieces (h: ptr) : slprop = parts h

ghost fn open_pieces (h: ptr)
  requires pieces h
  ensures parts h
{
  unfold pieces h
}

ghost fn close_pieces (h: ptr)
  requires parts h
  ensures pieces h
{
  fold pieces h
}

(* The slot is written next. *)
ghost fn clear_slot (h: ptr) (#p: ptr)
  requires ptr_pts_to (h +! struct_holder_offsetof_slot) 1.0R p
  ensures ptr_pts_to_uninit (h +! struct_holder_offsetof_slot)
{
  ptr_forget (h +! struct_holder_offsetof_slot)
}
