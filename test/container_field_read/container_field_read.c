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

int32_t read_second_via_field(_plain int32_t *second)
    _preserves(_inline_pulse(
      exists* (pv: $type(struct pair)).
        pts_to $(_container_of(second, struct pair, second)) #1.0R pv **
        Struct_pair.struct_pair__pred
          (!$(_container_of(second, struct pair, second))) 1.0R))
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
