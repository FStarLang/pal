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

(* A byte copy of only the leading bytes of an object. Each witness decodes
   the low bits of the source representation; an exact-width integer has no
   trap representations, so any such prefix is a value. *)
let float64_uint32_prefix_value (x: float64) : U32.t =
  U32.uint_to_t (float64_bits x % pow2 32)

let float64_int32_prefix_value (x: float64) : I32.t =
  let n = float64_bits x % pow2 32 in
  I32.int_to_t (if n < pow2 31 then n else n - pow2 32)

let float64_uint32_prefix_repr (x: float64) (b: bytes)
  : Lemma (requires float64_t_repr x b)
          (ensures len b == 8 /\ uint32_t_repr (float64_uint32_prefix_value x) (slice b 0 4))
  = Enc.encode_prefix 8 4 None (float64_bits x)

let float64_int32_prefix_repr (x: float64) (b: bytes)
  : Lemma (requires float64_t_repr x b)
          (ensures len b == 8 /\ int32_t_repr (float64_int32_prefix_value x) (slice b 0 4))
  = Enc.encode_prefix 8 4 None (float64_bits x)

(* The other direction: bytes an integer was stored as, read as a float.
   Every bit pattern is a float on an Annex F target (`float32_of_bits`), so
   the value always exists; which one it is -- possibly a NaN -- is all the
   program learns. *)
let uint32_float32_value (x: U32.t) : float32 = float32_of_bits (U32.v x)

let uint64_float64_value (x: U64.t) : float64 = float64_of_bits (U64.v x)

let int32_float32_value (x: I32.t) : float32 = float32_of_bits (Enc.to_bits 32 (I32.v x))

let int64_float64_value (x: I64.t) : float64 = float64_of_bits (Enc.to_bits 64 (I64.v x))

let uint32_float32_repr (x: U32.t) (b: bytes)
  : Lemma (requires uint32_t_repr x b)
          (ensures float32_t_repr (uint32_float32_value x) b) = ()

let uint64_float64_repr (x: U64.t) (b: bytes)
  : Lemma (requires uint64_t_repr x b)
          (ensures float64_t_repr (uint64_float64_value x) b) = ()

let int32_float32_repr (x: I32.t) (b: bytes)
  : Lemma (requires int32_t_repr x b)
          (ensures float32_t_repr (int32_float32_value x) b) = ()

let int64_float64_repr (x: I64.t) (b: bytes)
  : Lemma (requires int64_t_repr x b)
          (ensures float64_t_repr (int64_float64_value x) b) = ()

let copy_read_ok (dst src: ET.etypes) (ct: ET.ctype)
  : Lemma
      (requires ET.copy_complete_ok (ET.Ready dst) (ET.Ready src) /\
        (ET.declared_destination dst ==> ET.read_ok dst ct) /\
        (not (ET.declared_destination dst) ==> ET.read_ok src ct))
      (ensures ET.read_ok
        (ET.state_etypes (ET.complete_copy (ET.Ready dst) (ET.Ready src))) ct)
  = ()
