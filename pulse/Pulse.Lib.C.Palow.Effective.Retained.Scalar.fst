module Pulse.Lib.C.Palow.Effective.Retained.Scalar

#lang-pulse
open Pulse
open Pulse.Lib.C.Palow.Ptr
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes

module R = Pulse.Lib.C.Palow.Effective.Retained
module M = Pulse.Lib.C.Palow.Machine
module C = Pulse.Lib.C.Palow.Effective.Context

let uint32_t_read_field = C.read_field uint32_t_ctype uint32_t_repr uint32_t_alignof M.uint32_t_read_at
let uint32_t_write_field = C.write_field uint32_t_ctype uint32_t_repr uint32_t_alignof M.uint32_t_write_uninit_at
let uint32_t_write_uninit_field = C.write_uninit_field uint32_t_ctype uint32_t_repr uint32_t_alignof M.uint32_t_write_uninit_at
let uint32_t_forget_field = C.forget uint32_t_ctype uint32_t_repr uint32_t_alignof

let uint8_t_read_field = C.read_field uint8_t_ctype uint8_t_repr uint8_t_alignof M.uint8_t_read_at
let uint8_t_write_field = C.write_field uint8_t_ctype uint8_t_repr uint8_t_alignof M.uint8_t_write_uninit_at
let uint8_t_write_uninit_field = C.write_uninit_field uint8_t_ctype uint8_t_repr uint8_t_alignof M.uint8_t_write_uninit_at
let uint8_t_forget_field = C.forget uint8_t_ctype uint8_t_repr uint8_t_alignof

let ptr_read_field = C.read_field ptr_ctype ptr_repr ptr_alignof M.ptr_read_at
let ptr_write_field = C.write_field ptr_ctype ptr_repr ptr_alignof M.ptr_write_uninit_at
let ptr_write_uninit_field = C.write_uninit_field ptr_ctype ptr_repr ptr_alignof M.ptr_write_uninit_at
let ptr_forget_field = C.forget ptr_ctype ptr_repr ptr_alignof

let bool_t_read_field = C.read_field bool_t_ctype bool_t_repr bool_t_alignof M.bool_t_read_at
let bool_t_write_field = C.write_field bool_t_ctype bool_t_repr bool_t_alignof M.bool_t_write_uninit_at
let bool_t_write_uninit_field = C.write_uninit_field bool_t_ctype bool_t_repr bool_t_alignof M.bool_t_write_uninit_at
let bool_t_forget_field = C.forget bool_t_ctype bool_t_repr bool_t_alignof

let int8_t_read_field = C.read_field int8_t_ctype int8_t_repr int8_t_alignof M.int8_t_read_at
let int8_t_write_field = C.write_field int8_t_ctype int8_t_repr int8_t_alignof M.int8_t_write_uninit_at
let int8_t_write_uninit_field = C.write_uninit_field int8_t_ctype int8_t_repr int8_t_alignof M.int8_t_write_uninit_at
let int8_t_forget_field = C.forget int8_t_ctype int8_t_repr int8_t_alignof

let int16_t_read_field = C.read_field int16_t_ctype int16_t_repr int16_t_alignof M.int16_t_read_at
let int16_t_write_field = C.write_field int16_t_ctype int16_t_repr int16_t_alignof M.int16_t_write_uninit_at
let int16_t_write_uninit_field = C.write_uninit_field int16_t_ctype int16_t_repr int16_t_alignof M.int16_t_write_uninit_at
let int16_t_forget_field = C.forget int16_t_ctype int16_t_repr int16_t_alignof

let int32_t_read_field = C.read_field int32_t_ctype int32_t_repr int32_t_alignof M.int32_t_read_at
let int32_t_write_field = C.write_field int32_t_ctype int32_t_repr int32_t_alignof M.int32_t_write_uninit_at
let int32_t_write_uninit_field = C.write_uninit_field int32_t_ctype int32_t_repr int32_t_alignof M.int32_t_write_uninit_at
let int32_t_forget_field = C.forget int32_t_ctype int32_t_repr int32_t_alignof

let int64_t_read_field = C.read_field int64_t_ctype int64_t_repr int64_t_alignof M.int64_t_read_at
let int64_t_write_field = C.write_field int64_t_ctype int64_t_repr int64_t_alignof M.int64_t_write_uninit_at
let int64_t_write_uninit_field = C.write_uninit_field int64_t_ctype int64_t_repr int64_t_alignof M.int64_t_write_uninit_at
let int64_t_forget_field = C.forget int64_t_ctype int64_t_repr int64_t_alignof

let uint16_t_read_field = C.read_field uint16_t_ctype uint16_t_repr uint16_t_alignof M.uint16_t_read_at
let uint16_t_write_field = C.write_field uint16_t_ctype uint16_t_repr uint16_t_alignof M.uint16_t_write_uninit_at
let uint16_t_write_uninit_field = C.write_uninit_field uint16_t_ctype uint16_t_repr uint16_t_alignof M.uint16_t_write_uninit_at
let uint16_t_forget_field = C.forget uint16_t_ctype uint16_t_repr uint16_t_alignof

let uint64_t_read_field = C.read_field uint64_t_ctype uint64_t_repr uint64_t_alignof M.uint64_t_read_at
let uint64_t_write_field = C.write_field uint64_t_ctype uint64_t_repr uint64_t_alignof M.uint64_t_write_uninit_at
let uint64_t_write_uninit_field = C.write_uninit_field uint64_t_ctype uint64_t_repr uint64_t_alignof M.uint64_t_write_uninit_at
let uint64_t_forget_field = C.forget uint64_t_ctype uint64_t_repr uint64_t_alignof

let size_t_read_field = C.read_field size_t_ctype size_t_repr size_t_alignof M.size_t_read_at
let size_t_write_field = C.write_field size_t_ctype size_t_repr size_t_alignof M.size_t_write_uninit_at
let size_t_write_uninit_field = C.write_uninit_field size_t_ctype size_t_repr size_t_alignof M.size_t_write_uninit_at
let size_t_forget_field = C.forget size_t_ctype size_t_repr size_t_alignof

let float32_t_read_field = C.read_field float32_t_ctype float32_t_repr float32_t_alignof M.float32_t_read_at
let float32_t_write_field = C.write_field float32_t_ctype float32_t_repr float32_t_alignof M.float32_t_write_uninit_at
let float32_t_write_uninit_field = C.write_uninit_field float32_t_ctype float32_t_repr float32_t_alignof M.float32_t_write_uninit_at
let float32_t_forget_field = C.forget float32_t_ctype float32_t_repr float32_t_alignof

let float64_t_read_field = C.read_field float64_t_ctype float64_t_repr float64_t_alignof M.float64_t_read_at
let float64_t_write_field = C.write_field float64_t_ctype float64_t_repr float64_t_alignof M.float64_t_write_uninit_at
let float64_t_write_uninit_field = C.write_uninit_field float64_t_ctype float64_t_repr float64_t_alignof M.float64_t_write_uninit_at
let float64_t_forget_field = C.forget float64_t_ctype float64_t_repr float64_t_alignof

let uint32_t_read_retained = R.read_retained uint32_t_ctype uint32_t_repr uint32_t_alignof M.uint32_t_read_at
let uint32_t_write_retained = R.write_retained uint32_t_ctype uint32_t_repr uint32_t_alignof M.uint32_t_write_uninit_at
let uint32_t_write_uninit_retained = R.write_uninit_retained uint32_t_ctype uint32_t_repr uint32_t_alignof M.uint32_t_write_uninit_at
let uint32_t_forget_retained = R.forget uint32_t_ctype uint32_t_repr uint32_t_alignof
let uint32_t_reveal_uninit_retained = R.reveal_storage uint32_t_ctype uint32_t_alignof
let uint32_t_retain = R.retain_opaque uint32_t_ctype uint32_t_repr uint32_t_alignof uint32_t_repr_len uint32_t_pts_to uint32_t_reveal
let uint32_t_release_retained = R.release_opaque uint32_t_ctype uint32_t_repr uint32_t_alignof uint32_t_pts_to uint32_t_conceal

let uint8_t_read_retained = R.read_retained uint8_t_ctype uint8_t_repr uint8_t_alignof M.uint8_t_read_at
let uint8_t_write_retained = R.write_retained uint8_t_ctype uint8_t_repr uint8_t_alignof M.uint8_t_write_uninit_at
let uint8_t_write_uninit_retained = R.write_uninit_retained uint8_t_ctype uint8_t_repr uint8_t_alignof M.uint8_t_write_uninit_at
let uint8_t_forget_retained = R.forget uint8_t_ctype uint8_t_repr uint8_t_alignof
let uint8_t_reveal_uninit_retained = R.reveal_storage uint8_t_ctype uint8_t_alignof
let uint8_t_retain = R.retain_opaque uint8_t_ctype uint8_t_repr uint8_t_alignof uint8_t_repr_len uint8_t_pts_to uint8_t_reveal
let uint8_t_release_retained = R.release_opaque uint8_t_ctype uint8_t_repr uint8_t_alignof uint8_t_pts_to uint8_t_conceal

let ptr_read_retained = R.read_retained ptr_ctype ptr_repr ptr_alignof M.ptr_read_at
let ptr_write_retained = R.write_retained ptr_ctype ptr_repr ptr_alignof M.ptr_write_uninit_at
let ptr_write_uninit_retained = R.write_uninit_retained ptr_ctype ptr_repr ptr_alignof M.ptr_write_uninit_at
let ptr_forget_retained = R.forget ptr_ctype ptr_repr ptr_alignof
let ptr_reveal_uninit_retained = R.reveal_storage ptr_ctype ptr_alignof
let ptr_retain = R.retain_opaque ptr_ctype ptr_repr ptr_alignof ptr_repr_len ptr_pts_to ptr_reveal
let ptr_release_retained = R.release_opaque ptr_ctype ptr_repr ptr_alignof ptr_pts_to ptr_conceal

let bool_t_read_retained = R.read_retained bool_t_ctype bool_t_repr bool_t_alignof M.bool_t_read_at
let bool_t_write_retained = R.write_retained bool_t_ctype bool_t_repr bool_t_alignof M.bool_t_write_uninit_at
let bool_t_write_uninit_retained = R.write_uninit_retained bool_t_ctype bool_t_repr bool_t_alignof M.bool_t_write_uninit_at
let bool_t_forget_retained = R.forget bool_t_ctype bool_t_repr bool_t_alignof
let bool_t_reveal_uninit_retained = R.reveal_storage bool_t_ctype bool_t_alignof
let bool_t_retain = R.retain_opaque bool_t_ctype bool_t_repr bool_t_alignof bool_t_repr_len bool_t_pts_to bool_t_reveal
let bool_t_release_retained = R.release_opaque bool_t_ctype bool_t_repr bool_t_alignof bool_t_pts_to bool_t_conceal

let int8_t_read_retained = R.read_retained int8_t_ctype int8_t_repr int8_t_alignof M.int8_t_read_at
let int8_t_write_retained = R.write_retained int8_t_ctype int8_t_repr int8_t_alignof M.int8_t_write_uninit_at
let int8_t_write_uninit_retained = R.write_uninit_retained int8_t_ctype int8_t_repr int8_t_alignof M.int8_t_write_uninit_at
let int8_t_forget_retained = R.forget int8_t_ctype int8_t_repr int8_t_alignof
let int8_t_reveal_uninit_retained = R.reveal_storage int8_t_ctype int8_t_alignof
let int8_t_retain = R.retain_opaque int8_t_ctype int8_t_repr int8_t_alignof int8_t_repr_len int8_t_pts_to int8_t_reveal
let int8_t_release_retained = R.release_opaque int8_t_ctype int8_t_repr int8_t_alignof int8_t_pts_to int8_t_conceal

let int16_t_read_retained = R.read_retained int16_t_ctype int16_t_repr int16_t_alignof M.int16_t_read_at
let int16_t_write_retained = R.write_retained int16_t_ctype int16_t_repr int16_t_alignof M.int16_t_write_uninit_at
let int16_t_write_uninit_retained = R.write_uninit_retained int16_t_ctype int16_t_repr int16_t_alignof M.int16_t_write_uninit_at
let int16_t_forget_retained = R.forget int16_t_ctype int16_t_repr int16_t_alignof
let int16_t_reveal_uninit_retained = R.reveal_storage int16_t_ctype int16_t_alignof
let int16_t_retain = R.retain_opaque int16_t_ctype int16_t_repr int16_t_alignof int16_t_repr_len int16_t_pts_to int16_t_reveal
let int16_t_release_retained = R.release_opaque int16_t_ctype int16_t_repr int16_t_alignof int16_t_pts_to int16_t_conceal

let int32_t_read_retained = R.read_retained int32_t_ctype int32_t_repr int32_t_alignof M.int32_t_read_at
let int32_t_write_retained = R.write_retained int32_t_ctype int32_t_repr int32_t_alignof M.int32_t_write_uninit_at
let int32_t_write_uninit_retained = R.write_uninit_retained int32_t_ctype int32_t_repr int32_t_alignof M.int32_t_write_uninit_at
let int32_t_forget_retained = R.forget int32_t_ctype int32_t_repr int32_t_alignof
let int32_t_reveal_uninit_retained = R.reveal_storage int32_t_ctype int32_t_alignof
let int32_t_retain = R.retain_opaque int32_t_ctype int32_t_repr int32_t_alignof int32_t_repr_len int32_t_pts_to int32_t_reveal
let int32_t_release_retained = R.release_opaque int32_t_ctype int32_t_repr int32_t_alignof int32_t_pts_to int32_t_conceal

let int64_t_read_retained = R.read_retained int64_t_ctype int64_t_repr int64_t_alignof M.int64_t_read_at
let int64_t_write_retained = R.write_retained int64_t_ctype int64_t_repr int64_t_alignof M.int64_t_write_uninit_at
let int64_t_write_uninit_retained = R.write_uninit_retained int64_t_ctype int64_t_repr int64_t_alignof M.int64_t_write_uninit_at
let int64_t_forget_retained = R.forget int64_t_ctype int64_t_repr int64_t_alignof
let int64_t_reveal_uninit_retained = R.reveal_storage int64_t_ctype int64_t_alignof
let int64_t_retain = R.retain_opaque int64_t_ctype int64_t_repr int64_t_alignof int64_t_repr_len int64_t_pts_to int64_t_reveal
let int64_t_release_retained = R.release_opaque int64_t_ctype int64_t_repr int64_t_alignof int64_t_pts_to int64_t_conceal

let uint16_t_read_retained = R.read_retained uint16_t_ctype uint16_t_repr uint16_t_alignof M.uint16_t_read_at
let uint16_t_write_retained = R.write_retained uint16_t_ctype uint16_t_repr uint16_t_alignof M.uint16_t_write_uninit_at
let uint16_t_write_uninit_retained = R.write_uninit_retained uint16_t_ctype uint16_t_repr uint16_t_alignof M.uint16_t_write_uninit_at
let uint16_t_forget_retained = R.forget uint16_t_ctype uint16_t_repr uint16_t_alignof
let uint16_t_reveal_uninit_retained = R.reveal_storage uint16_t_ctype uint16_t_alignof
let uint16_t_retain = R.retain_opaque uint16_t_ctype uint16_t_repr uint16_t_alignof uint16_t_repr_len uint16_t_pts_to uint16_t_reveal
let uint16_t_release_retained = R.release_opaque uint16_t_ctype uint16_t_repr uint16_t_alignof uint16_t_pts_to uint16_t_conceal

let uint64_t_read_retained = R.read_retained uint64_t_ctype uint64_t_repr uint64_t_alignof M.uint64_t_read_at
let uint64_t_write_retained = R.write_retained uint64_t_ctype uint64_t_repr uint64_t_alignof M.uint64_t_write_uninit_at
let uint64_t_write_uninit_retained = R.write_uninit_retained uint64_t_ctype uint64_t_repr uint64_t_alignof M.uint64_t_write_uninit_at
let uint64_t_forget_retained = R.forget uint64_t_ctype uint64_t_repr uint64_t_alignof
let uint64_t_reveal_uninit_retained = R.reveal_storage uint64_t_ctype uint64_t_alignof
let uint64_t_retain = R.retain_opaque uint64_t_ctype uint64_t_repr uint64_t_alignof uint64_t_repr_len uint64_t_pts_to uint64_t_reveal
let uint64_t_release_retained = R.release_opaque uint64_t_ctype uint64_t_repr uint64_t_alignof uint64_t_pts_to uint64_t_conceal

(* long long / unsigned long long: the same representation as int64_t /
   uint64_t, but distinct effective types (6.2.5p4; 6.2.7p1). *)

let long_long_t_read_field = C.read_field long_long_t_ctype long_long_t_repr long_long_t_alignof M.long_long_t_read_at
let long_long_t_write_field = C.write_field long_long_t_ctype long_long_t_repr long_long_t_alignof M.long_long_t_write_uninit_at
let long_long_t_write_uninit_field = C.write_uninit_field long_long_t_ctype long_long_t_repr long_long_t_alignof M.long_long_t_write_uninit_at
let long_long_t_forget_field = C.forget long_long_t_ctype long_long_t_repr long_long_t_alignof

let ulong_long_t_read_field = C.read_field ulong_long_t_ctype ulong_long_t_repr ulong_long_t_alignof M.ulong_long_t_read_at
let ulong_long_t_write_field = C.write_field ulong_long_t_ctype ulong_long_t_repr ulong_long_t_alignof M.ulong_long_t_write_uninit_at
let ulong_long_t_write_uninit_field = C.write_uninit_field ulong_long_t_ctype ulong_long_t_repr ulong_long_t_alignof M.ulong_long_t_write_uninit_at
let ulong_long_t_forget_field = C.forget ulong_long_t_ctype ulong_long_t_repr ulong_long_t_alignof

let long_long_t_read_retained = R.read_retained long_long_t_ctype long_long_t_repr long_long_t_alignof M.long_long_t_read_at
let long_long_t_write_retained = R.write_retained long_long_t_ctype long_long_t_repr long_long_t_alignof M.long_long_t_write_uninit_at
let long_long_t_write_uninit_retained = R.write_uninit_retained long_long_t_ctype long_long_t_repr long_long_t_alignof M.long_long_t_write_uninit_at
let long_long_t_forget_retained = R.forget long_long_t_ctype long_long_t_repr long_long_t_alignof
let long_long_t_reveal_uninit_retained = R.reveal_storage long_long_t_ctype long_long_t_alignof
let long_long_t_retain = R.retain_opaque long_long_t_ctype long_long_t_repr long_long_t_alignof long_long_t_repr_len long_long_t_pts_to long_long_t_reveal
let long_long_t_release_retained = R.release_opaque long_long_t_ctype long_long_t_repr long_long_t_alignof long_long_t_pts_to long_long_t_conceal

let ulong_long_t_read_retained = R.read_retained ulong_long_t_ctype ulong_long_t_repr ulong_long_t_alignof M.ulong_long_t_read_at
let ulong_long_t_write_retained = R.write_retained ulong_long_t_ctype ulong_long_t_repr ulong_long_t_alignof M.ulong_long_t_write_uninit_at
let ulong_long_t_write_uninit_retained = R.write_uninit_retained ulong_long_t_ctype ulong_long_t_repr ulong_long_t_alignof M.ulong_long_t_write_uninit_at
let ulong_long_t_forget_retained = R.forget ulong_long_t_ctype ulong_long_t_repr ulong_long_t_alignof
let ulong_long_t_reveal_uninit_retained = R.reveal_storage ulong_long_t_ctype ulong_long_t_alignof
let ulong_long_t_retain = R.retain_opaque ulong_long_t_ctype ulong_long_t_repr ulong_long_t_alignof ulong_long_t_repr_len ulong_long_t_pts_to ulong_long_t_reveal
let ulong_long_t_release_retained = R.release_opaque ulong_long_t_ctype ulong_long_t_repr ulong_long_t_alignof ulong_long_t_pts_to ulong_long_t_conceal

let size_t_read_retained = R.read_retained size_t_ctype size_t_repr size_t_alignof M.size_t_read_at
let size_t_write_retained = R.write_retained size_t_ctype size_t_repr size_t_alignof M.size_t_write_uninit_at
let size_t_write_uninit_retained = R.write_uninit_retained size_t_ctype size_t_repr size_t_alignof M.size_t_write_uninit_at
let size_t_forget_retained = R.forget size_t_ctype size_t_repr size_t_alignof
let size_t_reveal_uninit_retained = R.reveal_storage size_t_ctype size_t_alignof
let size_t_retain = R.retain_opaque size_t_ctype size_t_repr size_t_alignof size_t_repr_len size_t_pts_to size_t_reveal
let size_t_release_retained = R.release_opaque size_t_ctype size_t_repr size_t_alignof size_t_pts_to size_t_conceal

let float32_t_read_retained = R.read_retained float32_t_ctype float32_t_repr float32_t_alignof M.float32_t_read_at
let float32_t_write_retained = R.write_retained float32_t_ctype float32_t_repr float32_t_alignof M.float32_t_write_uninit_at
let float32_t_write_uninit_retained = R.write_uninit_retained float32_t_ctype float32_t_repr float32_t_alignof M.float32_t_write_uninit_at
let float32_t_forget_retained = R.forget float32_t_ctype float32_t_repr float32_t_alignof
let float32_t_reveal_uninit_retained = R.reveal_storage float32_t_ctype float32_t_alignof
let float32_t_retain = R.retain_opaque float32_t_ctype float32_t_repr float32_t_alignof float32_t_repr_len float32_t_pts_to float32_t_reveal
let float32_t_release_retained = R.release_opaque float32_t_ctype float32_t_repr float32_t_alignof float32_t_pts_to float32_t_conceal

let float64_t_read_retained = R.read_retained float64_t_ctype float64_t_repr float64_t_alignof M.float64_t_read_at
let float64_t_write_retained = R.write_retained float64_t_ctype float64_t_repr float64_t_alignof M.float64_t_write_uninit_at
let float64_t_write_uninit_retained = R.write_uninit_retained float64_t_ctype float64_t_repr float64_t_alignof M.float64_t_write_uninit_at
let float64_t_forget_retained = R.forget float64_t_ctype float64_t_repr float64_t_alignof
let float64_t_reveal_uninit_retained = R.reveal_storage float64_t_ctype float64_t_alignof
let float64_t_retain = R.retain_opaque float64_t_ctype float64_t_repr float64_t_alignof float64_t_repr_len float64_t_pts_to float64_t_reveal
let float64_t_release_retained = R.release_opaque float64_t_ctype float64_t_repr float64_t_alignof float64_t_pts_to float64_t_conceal
