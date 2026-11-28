module Obj_field
#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes
open Pulse.Lib.C.Palow.Machine
open Struct_obj

(* A share of one field of an object, and nothing else of it: the object as a
   whole is never a value here. *)
let field (o: ptr) : slprop =
  exists* (q: perm) (p: ptr). ptr_pts_to (o +! struct_obj_offsetof_pool) q p
