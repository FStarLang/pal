module Pulse.Lib.C.Palow.Copy

open Pulse.Lib.C.Palow.Bytes
open Pulse.Lib.C.Palow.Scalar
open Pulse.Lib.C.Palow.CTypes
open Pulse.Lib.C.Palow.Float

module ET = Pulse.Lib.C.Palow.Etype
module Enc = Pulse.Lib.C.Palow.Encoding
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I32 = FStar.Int32
module I64 = FStar.Int64

(* These witnesses decode already known object representations. They neither
   read C storage nor establish an effective type. Exact-width integers have
   no trap representations on the model's two's-complement target. *)
let float32_uint32_value (x: float32) : U32.t =
  U32.uint_to_t (float32_bits x)

let float64_uint64_value (x: float64) : U64.t =
  U64.uint_to_t (float64_bits x)

let float32_int32_value (x: float32) : I32.t =
  let n = float32_bits x in
  I32.int_to_t (if n < pow2 31 then n else n - pow2 32)

let float64_int64_value (x: float64) : I64.t =
  let n = float64_bits x in
  I64.int_to_t (if n < pow2 63 then n else n - pow2 64)

let float32_uint32_repr (x: float32) (b: bytes)
  : Lemma (requires float32_t_repr x b)
          (ensures uint32_t_repr (float32_uint32_value x) b) = ()

let float64_uint64_repr (x: float64) (b: bytes)
  : Lemma (requires float64_t_repr x b)
          (ensures uint64_t_repr (float64_uint64_value x) b) = ()

let float32_int32_repr (x: float32) (b: bytes)
  : Lemma (requires float32_t_repr x b)
          (ensures int32_t_repr (float32_int32_value x) b) = ()

let float64_int64_repr (x: float64) (b: bytes)
  : Lemma (requires float64_t_repr x b)
          (ensures int64_t_repr (float64_int64_value x) b) = ()

let copy_read_ok (dst src: ET.etypes) (ct: ET.ctype)
  : Lemma
      (requires ET.copy_complete_ok (ET.Ready dst) (ET.Ready src) /\
        (ET.declared_destination dst ==> ET.read_ok dst ct) /\
        (not (ET.declared_destination dst) ==> ET.read_ok src ct))
      (ensures ET.read_ok
        (ET.state_etypes (ET.complete_copy (ET.Ready dst) (ET.Ready src))) ct)
  = ()
