#include "pal.h"
#include <stdint.h>

_include_pulse(Effective_values,
  open Pulse.Lib.C.Palow.Encoding
  module V = Pulse.Lib.C.Palow.Effective.Value
  module EM = Pulse.Lib.C.Palow.Effective.Machine
  module ET = Pulse.Lib.C.Palow.Etype
  module U32 = FStar.UInt32
  module U8 = FStar.UInt8

  let pair_type = ET.TStruct "effective_pair" 8
    [(0, uint32_t_ctype); (4, uint32_t_ctype)]
  let pair_index = ET.etypes_of pair_type true
  let array_type = ET.TArr uint32_t_ctype 2
  let array_index = ET.etypes_of array_type false
  let union_type = ET.TUnion "effective_union" 4
    [(0, uint32_t_ctype); (0, float32_t_ctype)]
  let union_index = ET.etypes_of union_type true

  ghost fn struct_field (a: ptr) (#b: bytes) (#x: U32.t)
    requires mem_pts_to_at a 1.0R b (FStar.Seq.slice pair_index 4 8)
    requires pure (uint32_t_repr x b /\ len b == 4 /\ aligned a uint32_t_alignof)
    ensures V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a 1.0R x
              (FStar.Seq.slice pair_index 4 8)
  {
    V.claim_component pair_type uint32_t_ctype uint32_t_repr uint32_t_alignof
      a #1.0R #x #b #pair_index 4;
  }

  ghost fn array_element (a: ptr) (#b: bytes) (#x: U32.t)
    requires mem_pts_to_at a 1.0R b (FStar.Seq.slice array_index 4 8)
    requires pure (uint32_t_repr x b /\ len b == 4 /\ aligned a uint32_t_alignof)
    ensures V.value uint32_t_ctype uint32_t_repr uint32_t_alignof a 1.0R x
              (FStar.Seq.slice array_index 4 8)
  {
    V.claim_component array_type uint32_t_ctype uint32_t_repr uint32_t_alignof
      a #1.0R #x #b #array_index 4;
  }

  ghost fn union_member (a: ptr) (#b: bytes) (#x: float32)
    requires mem_pts_to_at a 1.0R b (FStar.Seq.slice union_index 0 4)
    requires pure (float32_t_repr x b /\ len b == 4 /\ aligned a float32_t_alignof)
    ensures V.value float32_t_ctype float32_t_repr float32_t_alignof a 1.0R x
              (FStar.Seq.slice union_index 0 4)
  {
    V.claim_component union_type float32_t_ctype float32_t_repr float32_t_alignof
      a #1.0R #x #b #union_index 0;
  }

  fn character_store (a: ptr) (x: U8.t)
    requires V.storage uint8_t_ctype uint8_t_alignof a (EM.fresh_index 1)
    ensures V.value uint8_t_ctype uint8_t_repr uint8_t_alignof a 1.0R x
              (EM.fresh_index 1)
  {
    V.write uint8_t_ctype uint8_t_repr uint8_t_alignof a x (encode 1 None (U8.v x));
  }
)
