#include "pal.h"

/* 6.5p7 where generated code actually meets it: the typed claim.
 *
 * `test/etype_access_ok` states the rule against `Etype` directly, through a
 * helper that takes `read_ok e u` as a hypothesis.  That shows the predicate
 * says the right thing, but not that anything asks it.  These two claims ask
 * it: `int8_t_claim_uninit` and `uint32_t_claim_uninit` are the generated
 * API, their precondition is `{t}_etype_ok`, and that unfolds to `read_ok`
 * against the index layer 0 carries.  Nothing here supplies `read_ok` as a
 * hypothesis -- it has to be earned from the index.
 *
 * The index is the one a store leaves behind.  The storage was allocated, so
 * it had no declared type and none of its own; a store through an `int32_t`
 * lvalue gives it `int32_t` (6.5p6's third rule, `store_etypes`).  6.5p7 then
 * lists the lvalue types a later access may use, and these are two of them:
 *
 *   - `uint32_t` is "the signed or unsigned type corresponding to the
 *     effective type of the object" (bullet 3), so it is claimable at the
 *     full width; and
 *   - `int8_t` is "a character type" (the final bullet), so any single byte
 *     of the object is claimable as one.
 *
 * `test/etype_claim_bad` is the same claim at `bool_t`, which is on none of
 * the bullets, and is expected to fail.  Without that twin this file would
 * still pass if `{t}_etype_ok` were trivially true.
 */

_include_pulse(M,
  include Pulse.Lib.C.Palow.Ptr
  include Pulse.Lib.C.Palow.Bytes
  include Pulse.Lib.C.Palow
  include Pulse.Lib.C.Palow.CTypes
  include Pulse.Lib.C.Palow.Scalar
  module ET = Pulse.Lib.C.Palow.Etype

  (* Bullet 3: the corresponding unsigned type, at the full width. *)
  ghost fn claim_an_int_as_unsigned (a: ptr) (#b: bytes)
    (#e0: ET.etypes { ET.elen e0 == ET.csize int32_t_ctype })
    requires mem_pts_to_at a 1.0R b (ET.store_etypes e0 int32_t_ctype)
    requires pure (aligned a max_align)
    requires pure (len b == FStar.SizeT.v uint32_t_sizeof)
    requires pure (ET.allocated e0)
    ensures  uint32_t_pts_to_uninit a
  {
    aligned_divides a max_align uint32_t_alignof;
    ET.allocated_store_ok e0 int32_t_ctype;
    ET.store_ok_read_ok e0 int32_t_ctype;
    ET.allocated_store_etypes e0 int32_t_ctype;
    ET.read_ok_sub (ET.store_etypes e0 int32_t_ctype) int32_t_ctype 0 uint32_t_ctype;
    FStar.Seq.lemma_eq_elim
      (FStar.Seq.slice (ET.store_etypes e0 int32_t_ctype) 0 (ET.csize uint32_t_ctype))
      (ET.store_etypes e0 int32_t_ctype);
    uint32_t_claim_uninit a;
  }

  (* The final bullet: a character type, one byte of the object at a time.
     `aligned` needs no help here -- `aligned_one` discharges it. *)
  ghost fn claim_a_byte_of_an_int (a: ptr) (#b: bytes)
    (#e0: ET.etypes { ET.elen e0 == ET.csize int32_t_ctype })
    requires mem_pts_to_at a 1.0R b
               (FStar.Seq.slice (ET.store_etypes e0 int32_t_ctype) 0 1)
    requires pure (len b == 1)
    requires pure (ET.allocated e0)
    ensures  int8_t_pts_to_uninit a
  {
    ET.allocated_store_ok e0 int32_t_ctype;
    ET.store_ok_read_ok e0 int32_t_ctype;
    ET.allocated_store_etypes e0 int32_t_ctype;
    ET.read_ok_sub (ET.store_etypes e0 int32_t_ctype) int32_t_ctype 0 int8_t_ctype;
    int8_t_claim_uninit a;
  }
)

void etype_claim_ok(void)
{
}
