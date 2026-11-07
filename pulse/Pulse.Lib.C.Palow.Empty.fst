module Pulse.Lib.C.Palow.Empty

(* ---------------------------------------------------------------------------
   Objects of size zero.

   `struct empty { };` is not standard C, but GCC and Clang both accept it and
   real code uses it, so PAL has to translate it. Such an object owns no bytes,
   which means its points-to must be introducible from nothing and discardable
   into nothing -- otherwise there would be no way to obtain it in the first
   place, and nothing to do with it once a containing object is taken apart.

   Both directions are `mem_pts_to_empty`, packaged as ghost steps so that
   generated code can call them rather than rewrite with an slprop equality.
   --------------------------------------------------------------------------- *)

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow

(* The range is given explicitly rather than existentially quantified: the
   caller is a `_conceal` that already knows which (empty) slice of the
   enclosing object it means, and an existential here would not match it. *)
ghost fn mem_pts_to_nil (a: ptr) (p: perm) (b: bytes)
  requires pure (len b == 0)
  ensures  mem_pts_to a p b
{
  mem_pts_to_empty a p b;
  rewrite emp as (mem_pts_to a p b);
}

ghost fn drop_mem_pts_to_nil (a: ptr) (#p: perm) (#b: bytes)
  requires mem_pts_to a p b
  requires pure (len b == 0)
  ensures  emp
{
  mem_pts_to_empty a p b;
  rewrite (mem_pts_to a p b) as emp;
}
