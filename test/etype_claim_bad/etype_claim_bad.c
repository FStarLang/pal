#include "pal.h"

/* A negative test.  Verification of this file is *expected to fail*, and the
 * `should-fail` marker next to it names the message that has to appear.
 *
 * This is `test/etype_claim_ok`'s second claim with one type changed.  There,
 * a byte of storage whose effective type a store had set to `int32_t` was
 * claimed as an `int8_t`, which 6.5p7 permits outright -- "a character type"
 * is the last bullet on its list.  Here the claim is at `bool_t`, which is on
 * none of the bullets: `_Bool` is not `int32_t`, not a qualified version of
 * it, not its signed-or-unsigned counterpart, not an aggregate or union
 * containing one, and not a character type.
 *
 * So the access is undefined, and `bool_t_claim_uninit` has no way through.
 * The step that carries `etype_claim_ok` across is `ET.read_ok_sub`, and it
 * is absent here because its `access_ok` side condition is false -- there is
 * no other route to `bool_t_etype_ok`, which is what the failure says.
 *
 * Note what this test is *not* failing on.  The width is right (`_Bool` and
 * `int8_t` are both one byte), the alignment is right (`aligned_one`), and
 * the storage is owned outright at `1.0R`.  The only thing wrong with it is
 * the effective type, which is the point.
 */

_include_pulse(M,
  include Pulse.Lib.C.Palow.Ptr
  include Pulse.Lib.C.Palow.Bytes
  include Pulse.Lib.C.Palow
  include Pulse.Lib.C.Palow.CTypes
  module ET = Pulse.Lib.C.Palow.Etype

  ghost fn claim_a_byte_of_an_int_as_bool (a: ptr) (#b: bytes)
    (#e0: ET.etypes { ET.elen e0 == ET.csize int32_t_ctype })
    requires mem_pts_to_at a 1.0R b
               (FStar.Seq.slice (ET.store_etypes e0 int32_t_ctype) 0 1)
    requires pure (len b == 1)
    requires pure (ET.allocated e0)
    ensures  bool_t_pts_to_uninit a
  {
    ET.allocated_store_ok e0 int32_t_ctype;
    ET.store_ok_read_ok e0 int32_t_ctype;
    ET.allocated_store_etypes e0 int32_t_ctype;
    bool_t_claim_uninit a;
  }
)

void etype_claim_bad(void)
{
}
