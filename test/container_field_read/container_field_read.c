// Test (translated C): recover the enclosing struct from a pointer to one of
// its fields with `_container_of`, then read that *same* field back through the
// original pointer.
//
// When a caller holds only a pointer to an embedded field, it names ownership of
// the whole enclosing struct through that pointer, as `container(field)`. PAL
// therefore owns the field's cell addressed as the projection
// `second_1(container second)`. The direct read `*second` needs the cell
// addressed as `second`. Bridging the two is exactly the right-inverse
// round-trip `second_1(container second) == second` -- the per-field lemma PAL
// now emits (`struct_pair__second_proj_container_inv`). Delete that lemma and
// the `rewrite` in `expose_second` no longer typechecks, so this C function no
// longer verifies.
//
// This is the ownership move at the heart of MsQuic's
// QuicAckTrackerOnAckFrameAcked: it owns a QUIC_PACKET_SPACE via a pointer to
// its embedded ack-tracker and then operates on that tracker pointer directly.
//
// Only the field re-addressing is ghost (the Pulse frame matcher does not fire
// the round-trip SMTPat on its own -- it must be steered by a `rewrite`, whose
// residual equality goal the lemma discharges). The recovery and the read are
// ordinary translated C.

#include <stdint.h>
#include "pal.h"

struct pair {
    int32_t first;
    int32_t second;  // nonzero offset: a genuine (non-identity) pointer adjustment
};

#ifdef PALOW
/* In Palow a field's address is the structure's address plus the field's
   offset, and `_container_of` is the wrapping subtraction of that offset, so
   the two round trips are `add_sub_wrap` and `sub_wrap_add` rather than a pair
   of generated per-field lemmas. The one that matters here is the second, and
   it carries the side condition the old model's `ref` algebra hid: the offset
   has to be there to be taken back. The caller supplies that as a `pure` fact
   about the field pointer it was handed, which is the same thing ISO C
   requires of `container_of` -- that the pointer really points into such a
   structure. */
_include_pulse(Container_field_read_include,
  module P = Struct_pair
  open Pulse.Lib.C.Palow.Ptr

  // Focus the enclosing structure -- reached as `second -? off` -- down to the
  // `second` cell, then re-address that cell as the pointer the caller holds.
  // The frame matcher compares addresses as terms, so the `rewrite` is what
  // applies `sub_wrap_add`; its equality goal is closed by the `pure` premise.
  ghost fn expose_second (var_second: $type(int32_t *)) (#pv: erased P.struct_pair)
    requires P.struct_pair_pts_to (var_second -? P.struct_pair_offsetof_second) 1.0R pv
          ** pure (SizeT.v P.struct_pair_offsetof_second <= addr_of var_second)
    ensures  P.struct_pair_hole_second (var_second -? P.struct_pair_offsetof_second) 1.0R pv
          ** int32_t_pts_to var_second 1.0R pv.P.fld_second
  {
    P.struct_pair_focus_second (var_second -? P.struct_pair_offsetof_second);
    rewrite (int32_t_pts_to ((var_second -? P.struct_pair_offsetof_second) +! P.struct_pair_offsetof_second) 1.0R (reveal pv).P.fld_second)
         as (int32_t_pts_to var_second 1.0R (reveal pv).P.fld_second);
  }

  // Put it back, so what the caller preserved is what it gets.
  ghost fn hide_second (var_second: $type(int32_t *)) (#pv: erased P.struct_pair)
    requires P.struct_pair_hole_second (var_second -? P.struct_pair_offsetof_second) 1.0R pv
          ** int32_t_pts_to var_second 1.0R pv.P.fld_second
          ** pure (SizeT.v P.struct_pair_offsetof_second <= addr_of var_second)
    ensures  P.struct_pair_pts_to (var_second -? P.struct_pair_offsetof_second) 1.0R pv
  {
    rewrite (int32_t_pts_to var_second 1.0R (reveal pv).P.fld_second)
         as (int32_t_pts_to ((var_second -? P.struct_pair_offsetof_second) +! P.struct_pair_offsetof_second) 1.0R (reveal pv).P.fld_second);
    P.struct_pair_unfocus_read_second (var_second -? P.struct_pair_offsetof_second);
  }
)
#else
_include_pulse(Container_field_read_include,
  module P = Struct_pair

  // Re-address the `second` cell from the container projection
  // `second_1(container second)` to the original pointer `second`. The
  // `rewrite`'s ref-equality goal is closed by the emitted right-inverse lemma.
  ghost fn expose_second (var_second: $type(int32_t *))
    requires
      (exists* (sv: $type(int32_t)).
         pts_to (P.struct_pair__second_1
                   (P.struct_pair__second_container var_second)) #1.0R sv)
    ensures (exists* (sv: $type(int32_t)). pts_to var_second #1.0R sv)
  {
    with sv. rewrite (pts_to (P.struct_pair__second_1
                                (P.struct_pair__second_container var_second)) #1.0R sv)
                  as (pts_to var_second #1.0R sv);
  }

  // Re-address it back, so the caller's container-named ownership is restored.
  ghost fn hide_second (var_second: $type(int32_t *))
    requires (exists* (sv: $type(int32_t)). pts_to var_second #1.0R sv)
    ensures
      (exists* (sv: $type(int32_t)).
         pts_to (P.struct_pair__second_1
                   (P.struct_pair__second_container var_second)) #1.0R sv)
  {
    with sv. rewrite (pts_to var_second #1.0R sv)
                  as (pts_to (P.struct_pair__second_1
                                (P.struct_pair__second_container var_second)) #1.0R sv);
  }
)
#endif

#ifdef PALOW
int32_t read_second_via_field(_plain int32_t *second)
    _preserves(_inline_pulse(
      (exists* (pv: Struct_pair.struct_pair).
         Struct_pair.struct_pair_pts_to $(_container_of(second, struct pair, second)) 1.0R pv) **
      pure (SizeT.v Struct_pair.struct_pair_offsetof_second <=
              Pulse.Lib.C.Palow.Ptr.addr_of $(second))))
#else
int32_t read_second_via_field(_plain int32_t *second)
    _preserves(_inline_pulse(
      exists* (pv: $type(struct pair)).
        pts_to $(_container_of(second, struct pair, second)) #1.0R pv **
        Struct_pair.struct_pair__pred
          (!$(_container_of(second, struct pair, second))) 1.0R))
#endif
{
    struct pair *parent = _container_of(second, struct pair, second);
    // Recovery (`parent`) is the container-addressed handle; the read below goes
    // through the original field pointer instead. Re-addressing the `second`
    // cell between the two forms is what needs the right-inverse lemma.
    _ghost_stmt(Container_field_read_include.expose_second $(second));
    int32_t s = *second;
    _ghost_stmt(Container_field_read_include.hide_second $(second));
    return s;
}
