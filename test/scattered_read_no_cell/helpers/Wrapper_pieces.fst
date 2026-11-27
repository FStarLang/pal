module Wrapper_pieces
#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes
open Pulse.Lib.C.Palow.Machine
open Struct_wrapper
open Struct_params

(* As in `scattered_read`, but without the `request` field at all. The
   object is still in pieces; the piece the read needs is not held. *)
unfold let parts (w: ptr) : slprop =
  struct_wrapper_padding w 1.0R **

  struct_params_padding (w +! struct_wrapper_offsetof_inner) 1.0R **
  (exists* (f: ptr). ptr_pts_to (w +! struct_wrapper_offsetof_inner +! struct_params_offsetof_filter) 1.0R f) **
  (exists* (c: ptr). ptr_pts_to (w +! struct_wrapper_offsetof_inner +! struct_params_offsetof_cursor) 1.0R c) **
  uint32_t_pts_to_uninit (w +! struct_wrapper_offsetof_inner +! struct_params_offsetof_start) **
  (exists* (s: FStar.Int32.t). int32_t_pts_to (w +! struct_wrapper_offsetof_status) 1.0R s)

let pieces (w: ptr) : slprop = parts w

ghost fn open_pieces (w: ptr)
  requires pieces w
  ensures parts w
{
  unfold pieces w
}

ghost fn close_pieces (w: ptr)
  requires parts w
  ensures pieces w
{
  fold pieces w
}
