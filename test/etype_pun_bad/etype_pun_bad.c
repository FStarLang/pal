#include "pal.h"
#include <stdint.h>

/* A *negative* effective-type test that fails for the right reason.
 *
 * Most of the undefined-behaviour cases in `test/_effective_type` are already
 * rejected by PAL, but by the ownership and alias analysis rather than by
 * C11 6.5p7 -- `*(float *)&i` fails because the contract does not grant the
 * dereferenced target, which it would also fail for if effective types did
 * not exist. A test pinned on that message would pass without testing
 * anything, and would keep passing if the rule were deleted.
 *
 * So this test goes under the translator's analysis and states the obligation
 * where enforcement will actually sit: on layer 0's `mem_pts_to_at`, which
 * carries the per-byte effective-type index. The `should-fail` file pins
 * `read_ok`, so the test fails if and only if the 6.5p7 rule is what rejects
 * it.
 *
 * The two types are deliberately the *same width*. `read_ok` also requires the
 * index to cover exactly `csize u` bytes, so reading a 4-byte `int32_t` as an
 * 8-byte `double` would fail on the width alone and would prove nothing about
 * effective types -- it would still fail with 6.5p7 deleted. `float` is four
 * bytes, so the width conjunct holds and the only thing left to reject the
 * read is the rule under test.
 *
 * `palow-only`: the old model has no index to state this against. */

_include_pulse(Etype_pun_bad_include,
  include Pulse.Lib.C.Palow.Ptr
  include Pulse.Lib.C.Palow.Bytes
  include Pulse.Lib.C.Palow
  module E = Pulse.Lib.C.Palow.Etype

  let ct_i32 : E.ctype = E.TScalar E.SInt32
  let ct_f32 : E.ctype = E.TScalar E.SFloat32

  (* The obligation a typed read will carry once enforcement is switched on:
     the index covering the bytes has to license an access at the type being
     read. Everything below is stated against this one function, so a failure
     is always a failure of `read_ok` and never of anything else. *)
  ghost fn read_at (a: ptr) (#p: perm) (#b: bytes) (#e: E.etypes) (u: E.ctype)
    preserves mem_pts_to_at a p b e
    requires  pure (E.read_ok e u)
  {
    ()
  }

  (* [UB] 14.1 of `test/_effective_type`: an object whose effective type is
     `int32_t` read as a `float`. The precondition says the bytes are a
     *declared* `int32_t` -- `fixed = true` -- which is what a local variable
     or a global has, and what the first rule of 6.5p6 makes permanent.

     Compare `counterpart_read` in `test/etype_access_ok`, which discharges
     this same obligation, with this same index, at `uint32_t`. The index does
     not reject every read; it rejects this one.

     This is the only failing obligation in the module, deliberately: F* stops
     at the first error, so a second one here would be shadowed and would
     silently never be tested. The store and memcpy rules get their own
     directories for that reason. *)
  ghost fn pun_declared_int_as_float (a: ptr) (#p: perm) (#b: bytes)
    preserves mem_pts_to_at a p b (E.etypes_of ct_i32 true)
  {
    read_at a ct_f32
  }
)

/* The whole test is in the Pulse block above; a translated C function has to
 * exist for there to be a module to put it in. */
int32_t identity(int32_t x)
  _ensures(_old(x) == x)
{
    return x;
}
