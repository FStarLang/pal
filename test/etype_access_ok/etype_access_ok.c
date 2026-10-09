#include "pal.h"
#include <stdint.h>

/* The positive control for `test/etype_pun_bad`.
 *
 * A negative test on its own proves very little: `etype_pun_bad` would still
 * fail as expected if `read_ok` were unprovable for *every* type, which is
 * exactly what a too-strong rule looks like. Enforcement that rejects all
 * programs is not enforcement. So this test puts the defined-behaviour cases
 * through the identical obligation -- the same `read_at` ghost function,
 * carrying the same `read_ok` precondition -- and requires them to verify.
 *
 * Together the two pin the rule from both sides: `etype_pun_bad` says 6.5p7
 * rejects the punning, and this says it does not reject the C that the
 * standard allows.
 *
 * `palow-only`: the old model has no index to state this against. */

_include_pulse(Etype_access_ok_include,
  include Pulse.Lib.C.Palow.Ptr
  include Pulse.Lib.C.Palow.Bytes
  include Pulse.Lib.C.Palow
  module E = Pulse.Lib.C.Palow.Etype

  let ct_i32 : E.ctype = E.TScalar E.SInt32
  let ct_u32 : E.ctype = E.TScalar E.SUInt32
  let ct_f64 : E.ctype = E.TScalar E.SFloat64
  let ct_char : E.ctype = E.TScalar E.SChar

  (* struct point { int32_t x; int32_t y; } *)
  let ct_point : E.ctype = E.TStruct "point" 8 [(0, ct_i32); (4, ct_i32)]

  (* The same obligation `etype_pun_bad` fails to discharge. *)
  ghost fn read_at (a: ptr) (#p: perm) (#b: bytes) (#e: E.etypes) (u: E.ctype)
    preserves mem_pts_to_at a p b e
    requires  pure (E.read_ok e u)
  {
    ()
  }

  (* [DEFINED] 1.2: a declared `int32_t` read through `unsigned int *`. This is
     the signed/unsigned counterpart rule of 6.5p7, and it is the case the
     model got wrong until `counterpart` was added -- before that this very
     line failed, rejecting a program the standard explicitly permits. *)
  ghost fn counterpart_read (a: ptr) (#p: perm) (#b: bytes)
    preserves mem_pts_to_at a p b (E.etypes_of ct_i32 true)
  {
    read_at a ct_u32
  }

  (* [DEFINED] 3.3: a member of a declared struct, read at its own offset.
     The index covering the whole object licenses the member access, which is
     what lets an aggregate hand out field permissions. *)
  ghost fn member_read (a: ptr) (#p: perm) (#b: bytes)
    preserves mem_pts_to_at a p b (Seq.slice (E.etypes_of ct_point true) 0 4)
  {
    read_at a ct_i32
  }

  (* [DEFINED] 2.1: any object may be inspected as characters, whatever its
     effective type and at whatever offset -- 6.5p7 bullet 5. Here the first
     byte of a declared `double`. *)
  ghost fn byte_read (a: ptr) (#p: perm) (#b: bytes)
    preserves mem_pts_to_at a p b (Seq.slice (E.etypes_of ct_f64 true) 0 1)
  {
    read_at a ct_char
  }

  (* [DEFINED] 4.1: allocated storage has no declared type, so a store gives it
     one and it may be read at that type afterwards. This is the legal sibling
     of the punning in `etype_pun_bad` -- the *same* operation, separated only
     by whether the index says `fixed`. *)
  ghost fn retype_allocated (a: ptr) (#b: bytes { len b == 8 })
    requires mem_pts_to_at a 1.0R b (E.etypes_none 8)
    ensures  mem_pts_to_at a 1.0R b (E.store_etypes (E.etypes_none 8) ct_f64)
  {
    mem_store_etypes a ct_f64;
    E.store_none_read_ok ct_f64;
    read_at a ct_f64
  }
)

/* The whole test is in the Pulse block above; a translated C function has to
 * exist for there to be a module to put it in. */
int32_t identity(int32_t x)
  _ensures(_old(x) == x)
{
    return x;
}
