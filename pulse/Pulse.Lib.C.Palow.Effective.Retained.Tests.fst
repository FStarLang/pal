module Pulse.Lib.C.Palow.Effective.Retained.Tests

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.Effective.Retained.Scalar

module R = Pulse.Lib.C.Palow.Effective.Retained
module ET = Pulse.Lib.C.Palow.Etype
module U32 = FStar.UInt32

fn ordinary_call (a: ptr) (#base: ET.etypes) (#x: erased U32.t)
  requires R.value uint32_t_ctype uint32_t_repr uint32_t_alignof a 1.0R x base
  ensures R.value uint32_t_ctype uint32_t_repr uint32_t_alignof a 1.0R 1ul base
{
  let _ = uint32_t_read_retained a;
  uint32_t_write_retained a 1ul;
}

fn ordinary_caller (a: ptr) (#x: erased U32.t)
  requires uint32_t_pts_to a 1.0R x
  ensures uint32_t_pts_to a 1.0R 1ul
{
  uint32_t_retain a;
  ordinary_call a;
  uint32_t_release_retained a;
}
