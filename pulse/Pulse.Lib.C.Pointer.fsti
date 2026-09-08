module Pulse.Lib.C.Pointer

open Pulse.Lib.C.CoreRef
module I = FStar.Int
module U = FStar.UInt

(* Derived modular projections, not new axioms. The width describes the
   destination integer type, never the pointer representation.
   The conditional equalities expose useful arithmetic without requiring
   callers to unfold modular division. There is no cross-width losslessness
   claim outside the destination's representable range. *)
val unsigned_view (width: pos) (p: core_ref)
  : u:U.uint_t width{
      u == core_address p % pow2 width /\
      (0 <= core_address p /\ core_address p < pow2 width ==>
        u == core_address p) /\
      (-pow2 width <= core_address p /\ core_address p < 0 ==>
        u == core_address p + pow2 width)}

val signed_view (width: pos) (p: core_ref)
  : s:I.int_t width{
      s == I.from_uint (unsigned_view width p) /\
      (I.fits (core_address p) width ==> s == core_address p)}

val null_address (p: core_ref)
  : Lemma
      (requires p == core_null)
      (ensures core_address p == 0)
      [SMTPat (core_address p)]
