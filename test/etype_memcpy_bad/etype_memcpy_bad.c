#include "pal.h"
#include <stdint.h>

/* [UB] 13.1 of `test/_effective_type`: `memcpy` cannot retype a declared
 * object.
 *
 * The third rule of 6.5p6 -- a byte copy gives the destination the source's
 * effective type -- is written "for all other accesses to an object having no
 * declared type", so it does not apply to a declared one. Copying the bytes of
 * a `double` over a declared `int32_t` therefore leaves the destination an
 * `int32_t`, and reading it back as a `double` is undefined.
 *
 * Had `memcpy` been modelled as plain index transport -- destination index
 * becomes source index, which is the obvious reading and was the comment in
 * `Pulse.Lib.C.Palow.Etype` before this -- the copy would have relabelled the
 * declared object and this read would verify. `copy_etypes` keeps a `fixed`
 * destination entry, and that is what this test pins.
 *
 * One failing obligation per directory: see `test/etype_store_bad`.
 *
 * `palow-only`: the old model has no index to state this against. */

_include_pulse(Etype_memcpy_bad_include,
  include Pulse.Lib.C.Palow.Ptr
  include Pulse.Lib.C.Palow.Bytes
  include Pulse.Lib.C.Palow
  module E = Pulse.Lib.C.Palow.Etype

  let ct_i32 : E.ctype = E.TScalar E.SInt32
  let ct_f32 : E.ctype = E.TScalar E.SFloat32

  ghost fn read_at (a: ptr) (#p: perm) (#b: bytes) (#e: E.etypes) (u: E.ctype)
    preserves mem_pts_to_at a p b e
    requires  pure (E.read_ok e u)
  {
    ()
  }

  (* The index side of `memcpy`: the destination index becomes `copy_etypes`
     of the two, which is *not* simply the source index.

     `admit()` stands in for the layer-0 ghost step that Stage 2 adds next to
     `mem_store_etypes`. What is under test here is the index rule, not the
     memory model, and the rule is `copy_etypes` either way. *)
  ghost fn copy_at (a: ptr) (#b: bytes) (#d: E.etypes)
                   (s: E.etypes { E.elen s == E.elen d })
    requires mem_pts_to_at a 1.0R b d
    ensures  mem_pts_to_at a 1.0R b (E.copy_etypes d s)
  {
    admit()
  }

  (* Copy a `float` over a declared `int32_t`, then read it back as a `float`.
     The destination keeps its declared type, so the read is rejected. *)
  ghost fn memcpy_then_read_as_float (a: ptr) (#b: bytes)
    requires mem_pts_to_at a 1.0R b (E.etypes_of ct_i32 true)
    ensures  mem_pts_to_at a 1.0R b
               (E.copy_etypes (E.etypes_of ct_i32 true)
                              (E.etypes_of ct_f32 false))
  {
    copy_at a (E.etypes_of ct_f32 false);
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
