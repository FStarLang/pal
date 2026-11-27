module Fill_head
#lang-pulse
open Pulse
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes
open Struct_lnk
open Struct_head

(* The author's step that takes back the pieces `fill_some` leaves: the two
   fields it wrote give up their values, and the object is storage again. *)
ghost fn release (h: ptr)
  requires (exists* (n: ptr). ptr_pts_to ((h +! struct_head_offsetof_list) +! struct_lnk_offsetof_next) 1.0R n) **
    ptr_pts_to_uninit ((h +! struct_head_offsetof_list) +! struct_lnk_offsetof_prev) **
    struct_lnk_padding (h +! struct_head_offsetof_list) 1.0R **
    (exists* (q: FStar.UInt32.t). uint32_t_pts_to (h +! struct_head_offsetof_qlen) 1.0R q) **
    int32_t_pts_to_uninit (h +! struct_head_offsetof_lock) **
    struct_head_padding h 1.0R
  ensures struct_head_pts_to_uninit h
{
  ptr_forget ((h +! struct_head_offsetof_list) +! struct_lnk_offsetof_next);
  uint32_t_forget (h +! struct_head_offsetof_qlen);
  struct_lnk_gather_uninit (h +! struct_head_offsetof_list);
  struct_head_gather_uninit h;
}
