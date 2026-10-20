#include "pal.h"
#include <stdint.h>

_include_pulse(Effective_machine,
  module EM = Pulse.Lib.C.Palow.Effective.Machine
  module Effective = Pulse.Lib.C.Palow.Effective
  module ET = Pulse.Lib.C.Palow.Etype

  fn prepared_store (a: ptr)
    requires Effective.prepared a uint32_t_ctype
    ensures mem_pts_to_at a 1.0R (zeroed 4)
              (ET.etypes_of uint32_t_ctype false)
  {
    EM.initialize a uint32_t_ctype (zeroed 4);
  }

  fn untyped_zero_reads (a: ptr)
    preserves mem_pts_to_at a 1.0R (zeroed 4) (EM.fresh_index 4)
  {
    let _ = EM.load a uint32_t_ctype;
    let _ = EM.load a int32_t_ctype;
    ();
  }

  fn prepared_copy (dst src: ptr) (#bs: erased bytes)
    preserves mem_pts_to_at src 0.5R bs (ET.etypes_of uint32_t_ctype true)
    requires Effective.prepared dst uint32_t_ctype
    requires pure (len bs == 4)
    ensures mem_pts_to_at dst 1.0R bs (ET.etypes_of uint32_t_ctype false)
  {
    EM.memcpy_prepared dst src 4sz uint32_t_ctype;
  }

  fn zero_preserves_type (a: ptr) (#b: erased bytes) (#e: ET.etypes)
    requires mem_pts_to_at a 1.0R b e
    requires pure (len b == 4 /\ ET.elen e == 4)
    ensures mem_pts_to_at a 1.0R (zeroed 4) e
  {
    EM.memset_zero a 4sz;
  }

  fn declared_cross_type_copy (dst src: ptr) (#bs #bd: erased bytes)
    preserves mem_pts_to_at src 0.5R bs (ET.etypes_of uint32_t_ctype true)
    requires mem_pts_to_at dst 1.0R bd (ET.etypes_of float32_t_ctype true)
    requires pure (len bs == 4 /\ len bd == 4)
    ensures mem_pts_to_at dst 1.0R bs (ET.etypes_of float32_t_ctype true)
  {
    EM.memcpy dst src 4sz;
    ET.complete_copy_declared_stable
      (ET.Ready (ET.etypes_of float32_t_ctype true))
      (ET.Ready (ET.etypes_of uint32_t_ctype true));
    rewrite (mem_pts_to_at dst 1.0R bs
      (ET.state_etypes (ET.complete_copy
        (ET.Ready (ET.etypes_of float32_t_ctype true))
        (ET.Ready (ET.etypes_of uint32_t_ctype true)))))
    as (mem_pts_to_at dst 1.0R bs (ET.etypes_of float32_t_ctype true));
  }

  ghost fn share_prefix (a: ptr)
    requires mem_pts_to_at a 1.0R (zeroed 4) (ET.etypes_of uint32_t_ctype true)
    ensures mem_pts_to_at a 0.5R (zeroed 4) (ET.etypes_of uint32_t_ctype true)
    ensures mem_pts_to_at a 0.5R (slice (zeroed 4) 0 1)
              (FStar.Seq.slice (ET.etypes_of uint32_t_ctype true) 0 1)
    ensures mem_pts_to_at (a +! 1sz) 0.5R (slice (zeroed 4) 1 4)
              (FStar.Seq.slice (ET.etypes_of uint32_t_ctype true) 1 4)
  {
    mem_share_at a;
    mem_split_at a #0.5R #(zeroed 4) #(ET.etypes_of uint32_t_ctype true) 1sz;
  }
)
