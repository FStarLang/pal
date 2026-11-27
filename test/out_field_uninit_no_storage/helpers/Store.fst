module Store
#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes
open Struct_report

(* All of `*a` but `counts`, as storage. The name ends in
   `struct_report_hole_...`, which makes PAL treat an assertion of it as a
   field loan. *)
let struct_report_hole_out (a: ptr) : slprop =
  uint32_t_pts_to_uninit (a +! struct_report_offsetof_kind) **
  struct_report_padding a 1.0R
