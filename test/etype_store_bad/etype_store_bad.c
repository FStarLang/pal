#include "pal.h"
#include <stdint.h>

/* [UB] 13.2 and 12.2 of `test/_effective_type`: a store at the wrong type into
 * an object that has a declared type.
 *
 * This is the rule that `store_etypes` alone does not give. `store_etypes`
 * says how a store *moves* the index, and on a declared object it moves it
 * nowhere -- `store_entry` leaves a `fixed` byte alone. Taken by itself that
 * reads as "the store is permitted and has no effect on the type", when what
 * C says is that the store is undefined behaviour. `store_ok` is the missing
 * side condition, and this test is what holds it in place.
 *
 * One failing obligation per directory: F* stops at the first error, so a
 * module with two would test only the first and silently drop the second.
 * The read rule is in `test/etype_pun_bad` and the memcpy rule in
 * `test/etype_memcpy_bad`.
 *
 * `int32_t` and `float` are both four bytes, deliberately. `store_ok` also
 * requires the index to cover exactly `csize u` bytes, so storing a `double`
 * here would fail on the width alone and would prove nothing about effective
 * types.
 *
 * `palow-only`: the old model has no index to state this against. */

_include_pulse(Etype_store_bad_include,
  include Pulse.Lib.C.Palow.Ptr
  include Pulse.Lib.C.Palow.Bytes
  include Pulse.Lib.C.Palow
  module E = Pulse.Lib.C.Palow.Etype

  let ct_i32 : E.ctype = E.TScalar E.SInt32
  let ct_f32 : E.ctype = E.TScalar E.SFloat32

  (* The obligation a typed write will carry once enforcement is switched on.
     Note that it needs full permission, which is already the rule for
     `mem_store_etypes`: storage you share cannot be retyped. *)
  ghost fn store_at (a: ptr) (#b: bytes) (#e: E.etypes)
                    (u: E.ctype { E.elen e == E.csize u })
    requires mem_pts_to_at a 1.0R b e ** pure (E.store_ok e u)
    ensures  mem_pts_to_at a 1.0R b (E.store_etypes e u)
  {
    mem_store_etypes a u
  }

  (* Storing a `float` into a declared `int32_t`. The positive sibling is
     `retype_allocated` in `test/etype_access_ok`, which performs the very same
     store into storage that has no declared type and is accepted -- the two
     differ only in whether the index says `fixed`. *)
  ghost fn store_float_into_declared_int (a: ptr) (#b: bytes)
    requires mem_pts_to_at a 1.0R b (E.etypes_of ct_i32 true)
    ensures  mem_pts_to_at a 1.0R b
               (E.store_etypes (E.etypes_of ct_i32 true) ct_f32)
  {
    store_at a ct_f32
  }
)

/* The whole test is in the Pulse block above; a translated C function has to
 * exist for there to be a module to put it in. */
int32_t identity(int32_t x)
  _ensures(_old(x) == x)
{
    return x;
}
