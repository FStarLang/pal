module Pulse.Lib.C.GNU.Elvis

(* The GNU `a ?: b` operator: `a` if it is nonzero, else `b`. PAL emits a
   C `a ?: b` as `elvis_<type> a b` *)

open Pulse.Lib.C.Casts.Bool

module Arr = Pulse.Lib.C.Array
module CR = Pulse.Lib.C.CoreRef
module PD = Pulse.Lib.C.PtrdiffT
module R = Pulse.Lib.Reference

unfold let elvis_int8 (a b: Int8.t) : Int8.t = if int8_to_bool a then a else b
unfold let elvis_int16 (a b: Int16.t) : Int16.t = if int16_to_bool a then a else b
unfold let elvis_int32 (a b: Int32.t) : Int32.t = if int32_to_bool a then a else b
unfold let elvis_int64 (a b: Int64.t) : Int64.t = if int64_to_bool a then a else b
unfold let elvis_uint8 (a b: UInt8.t) : UInt8.t = if uint8_to_bool a then a else b
unfold let elvis_uint16 (a b: UInt16.t) : UInt16.t = if uint16_to_bool a then a else b
unfold let elvis_uint32 (a b: UInt32.t) : UInt32.t = if uint32_to_bool a then a else b
unfold let elvis_uint64 (a b: UInt64.t) : UInt64.t = if uint64_to_bool a then a else b
unfold let elvis_size_t (a b: SizeT.t) : SizeT.t = if a = 0sz then b else a
unfold let elvis_ptrdiff_t (a b: PD.t) : PD.t =
  if a = PD.zero then b else a

(* A pointer is "nonzero" when it is not null. *)
unfold let elvis_ref (#t: Type) (a b: R.ref t) : R.ref t =
  if R.is_null a then b else a

unfold let elvis_core (a b: CR.core_ref) : CR.core_ref =
  if CR.core_is_null a then b else a

unfold let elvis_array (#t: Type) (a b: Arr.array t) : Arr.array t =
  if Arr.arrayptr_eq a Arr.array_null then b else a
