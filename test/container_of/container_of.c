// Test: PAL generates, for *every* struct field, the inverse of the
// field-address projection: a total `..._container` function mapping the
// field's `ref` (or, for an inline-array field, its array handle) back to a
// `ref` of the enclosing struct, plus TWO round-trip lemmas, each with an
// `SMTPat` on its round-trip term:
//   * left-inverse  `container (proj p) == p`  (`..._container_inv`)
//   * right-inverse `proj (container r) == r`  (`..._proj_container_inv`)
// The user composes `container_of` / `CXPLAT_CONTAINING_RECORD` out of these.
// The right-inverse lets a caller that reached the struct via
// `container_of(field_ref)` re-address the original field through its
// projection -- e.g. owning `packet_space` via a pointer to its embedded
// `tracker`, then framing `pts_to (proj (container tracker))` against
// `pts_to tracker`.
//
// `packet_space` exercises all field kinds: an embedded by-value aggregate
// (`tracker`, via a typedef), a scalar (`id`), a pointer (`back`), and an
// inline array (`data`). Each kind gets its own `..._container` symbol.
//
// The proofs live in `_include_pulse` rather than PAL surface syntax because
// they must name the generated F* symbols (e.g.
// `struct_packet_space__tracker_container`, `struct_packet_space__tracker_1`)
// directly; these address-level axioms have no C-level expression.

#include "pal.h"
#include <stdint.h>

struct ack_tracker {
  int32_t count;
};

typedef struct ack_tracker ack_tracker_t;

struct packet_space {
  ack_tracker_t tracker;
  int32_t id;
  int32_t *back;
  int32_t data[4];
};

/* Palow has no per-field `ref`, so it has no per-field `container` function
   and no pair of inverse lemmas to generate. A field's address *is* the
   structure's address plus the field's offset, and the recovery is the
   wrapping subtraction `( -? )` of that same offset, so the left inverse is
   one axiom (`add_sub_wrap`) that holds for every field of every structure at
   once. The lemmas below are the same statements as the `#else` branch,
   written against that. The right inverse -- `(p -? off) +! off == p` -- is
   deliberately *not* available: it would have to hold at NULL as well, where
   it forces `addr_of p >= off`, so a caller that reached a structure through a
   field re-addresses the field textually instead. */
_include_pulse(Container_of_include,
  module PS = Struct_packet_space
  open Pulse.Lib.C.Palow.Ptr

  // Recover the enclosing packet_space from a pointer to its embedded tracker.
  // No ownership is needed: taking and undoing an offset reads nothing.
  ghost
  fn get_from_tracker (ps: ptr)
    requires emp
    ensures pure ((ps +! PS.struct_packet_space_offsetof_tracker)
                    -? PS.struct_packet_space_offsetof_tracker == ps)
  { () }

  // Same recovery from a scalar field.
  ghost
  fn get_from_id (ps: ptr)
    requires emp
    ensures pure ((ps +! PS.struct_packet_space_offsetof_id)
                    -? PS.struct_packet_space_offsetof_id == ps)
  { () }

  // ... from a pointer field, whose cell holds a `ptr`.
  ghost
  fn get_from_back (ps: ptr)
    requires emp
    ensures pure ((ps +! PS.struct_packet_space_offsetof_back)
                    -? PS.struct_packet_space_offsetof_back == ps)
  { () }

  // ... and from an inline-array field, which in Palow is not a separate
  // handle but the address of the first element.
  ghost
  fn get_from_data (ps: ptr)
    requires emp
    ensures pure ((ps +! PS.struct_packet_space_offsetof_data)
                    -? PS.struct_packet_space_offsetof_data == ps)
  { () }

  // `tracker` sits at offset zero, so recovering the structure from it is the
  // identity even before the subtraction is undone. That is what keeps an
  // intrusive list's NULL terminator a NULL pointer across the recovery.
  ghost
  fn tracker_at_zero (q: ptr)
    requires emp
    ensures pure (q -? PS.struct_packet_space_offsetof_tracker == q)
  { () }

  // A caller that owns the packet_space and reached it through the embedded
  // field's address owns it at the recovered pointer. The two are the same
  // pointer, but the frame matcher compares addresses as terms and never calls
  // the solver, so a `rewrite` is what says so. This is why the *translator*
  // cancels the offset in the text it emits rather than relying on the axiom.
  ghost
  fn client_uses_recovered_pointer (ps: ptr) (#psv: erased PS.struct_packet_space)
    requires PS.struct_packet_space_pts_to ps 1.0R psv
    ensures PS.struct_packet_space_pts_to
              ((ps +! PS.struct_packet_space_offsetof_tracker)
                 -? PS.struct_packet_space_offsetof_tracker) 1.0R psv
  {
    rewrite (PS.struct_packet_space_pts_to ps 1.0R psv)
         as (PS.struct_packet_space_pts_to
               ((ps +! PS.struct_packet_space_offsetof_tracker)
                  -? PS.struct_packet_space_offsetof_tracker) 1.0R psv);
  }

  // The same bridge for a *field's* cell, which is the Palow counterpart of
  // the right-inverse lemma's only real use.
  ghost
  fn readdress_tracker_cell (ps: ptr) (#tv: erased Struct_ack_tracker.struct_ack_tracker)
    requires Struct_ack_tracker.struct_ack_tracker_pts_to
               ((ps +! PS.struct_packet_space_offsetof_tracker)
                  -? PS.struct_packet_space_offsetof_tracker) 1.0R tv
    ensures Struct_ack_tracker.struct_ack_tracker_pts_to ps 1.0R tv
  {
    rewrite (Struct_ack_tracker.struct_ack_tracker_pts_to
               ((ps +! PS.struct_packet_space_offsetof_tracker)
                  -? PS.struct_packet_space_offsetof_tracker) 1.0R tv)
         as (Struct_ack_tracker.struct_ack_tracker_pts_to ps 1.0R tv);
  }
)
