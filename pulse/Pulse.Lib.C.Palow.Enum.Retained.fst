module Pulse.Lib.C.Palow.Enum.Retained

(* Enumerated types (6.7.2.2). An enumerated type has the size, alignment and
   representation of its underlying integer type, here `unsigned int` or
   `int`, but it is a distinct type: its effective-type descriptor is
   `ET.SEnum tag base`, so two different enumerated types do not alias each
   other while either one may still be accessed through its underlying type or
   that type's signed/unsigned counterpart (6.5p7).

   One family per underlying type, parameterized by the enumeration's tag.
   PAL emits, per enumeration, an `Enum_<tag>` module of `unfold` aliases
   (`enum_u32_color_read = enum_u32_read "color"`, ...).

   Generated from the 16-bit blocks of Pulse.Lib.C.Palow.Effective.Retained.Scalar. *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes
module R = Pulse.Lib.C.Palow.Effective.Retained
module M = Pulse.Lib.C.Palow.Machine
module C = Pulse.Lib.C.Palow.Effective.Context
open Pulse.Lib.C.Palow.Enum.Base
open Pulse.Lib.C.Palow.Enum


let enum_u32_read_field (tag: string) = C.read_field (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) (enum_u32_read_at tag)
let enum_u32_write_field (tag: string) = C.write_field (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) (enum_u32_write_uninit_at tag)
let enum_u32_write_uninit_field (tag: string) = C.write_uninit_field (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) (enum_u32_write_uninit_at tag)
let enum_u32_forget_field (tag: string) = C.forget (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag)

let enum_u32_read_retained (tag: string) = R.read_retained (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) (enum_u32_read_at tag)
let enum_u32_write_retained (tag: string) = R.write_retained (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) (enum_u32_write_uninit_at tag)
let enum_u32_write_uninit_retained (tag: string) = R.write_uninit_retained (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) (enum_u32_write_uninit_at tag)
let enum_u32_forget_retained (tag: string) = R.forget (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag)
let enum_u32_reveal_uninit_retained (tag: string) = R.reveal_storage (enum_u32_ctype tag) (enum_u32_alignof tag)
let enum_u32_retain (tag: string) = R.retain_opaque (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) (enum_u32_repr_len tag) (enum_u32_pts_to tag) (enum_u32_reveal tag)
let enum_u32_release_retained (tag: string) = R.release_opaque (enum_u32_ctype tag) (enum_u32_repr tag) (enum_u32_alignof tag) (enum_u32_pts_to tag) (enum_u32_conceal tag)

let enum_i32_read_field (tag: string) = C.read_field (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) (enum_i32_read_at tag)
let enum_i32_write_field (tag: string) = C.write_field (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) (enum_i32_write_uninit_at tag)
let enum_i32_write_uninit_field (tag: string) = C.write_uninit_field (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) (enum_i32_write_uninit_at tag)
let enum_i32_forget_field (tag: string) = C.forget (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag)

let enum_i32_read_retained (tag: string) = R.read_retained (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) (enum_i32_read_at tag)
let enum_i32_write_retained (tag: string) = R.write_retained (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) (enum_i32_write_uninit_at tag)
let enum_i32_write_uninit_retained (tag: string) = R.write_uninit_retained (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) (enum_i32_write_uninit_at tag)
let enum_i32_forget_retained (tag: string) = R.forget (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag)
let enum_i32_reveal_uninit_retained (tag: string) = R.reveal_storage (enum_i32_ctype tag) (enum_i32_alignof tag)
let enum_i32_retain (tag: string) = R.retain_opaque (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) (enum_i32_repr_len tag) (enum_i32_pts_to tag) (enum_i32_reveal tag)
let enum_i32_release_retained (tag: string) = R.release_opaque (enum_i32_ctype tag) (enum_i32_repr tag) (enum_i32_alignof tag) (enum_i32_pts_to tag) (enum_i32_conceal tag)

