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

_include_pulse(Container_of_include,
  module PS = Struct_packet_space

  // Recover the enclosing packet_space from a pointer to its embedded tracker.
  // Ownership is supplied by the caller; the linkage `pure` fact says the
  // argument is exactly the projected field, and the generated inverse lemma's
  // SMTPat closes `r == ps`.
  fn get_from_tracker
      (#ps: $type(struct packet_space *))
      (var_tracker: $type(ack_tracker_t *))
    requires
      (exists* (psv: $type(struct packet_space)). pts_to ps #1.0R psv)
      ** pure (PS.struct_packet_space__tracker_1 ps == var_tracker)
    returns r: $type(struct packet_space *)
    ensures
      (exists* (psv: $type(struct packet_space)). pts_to ps #1.0R psv)
      ** pure (r == ps)
  {
    PS.struct_packet_space__tracker_container var_tracker
  }

  // Same recovery, but from a scalar field — exercises the non-aggregate case.
  fn get_from_id
      (#ps: $type(struct packet_space *))
      (var_id: $type(int32_t *))
    requires
      (exists* (psv: $type(struct packet_space)). pts_to ps #1.0R psv)
      ** pure (PS.struct_packet_space__id_1 ps == var_id)
    returns r: $type(struct packet_space *)
    ensures
      (exists* (psv: $type(struct packet_space)). pts_to ps #1.0R psv)
      ** pure (r == ps)
  {
    PS.struct_packet_space__id_container var_id
  }

  // Recovery from a pointer field — the projected `ref` is itself a `ref` of a
  // pointer cell (`int32_t **`).
  fn get_from_back
      (#ps: $type(struct packet_space *))
      (var_back: $type(int32_t **))
    requires
      (exists* (psv: $type(struct packet_space)). pts_to ps #1.0R psv)
      ** pure (PS.struct_packet_space__back_1 ps == var_back)
    returns r: $type(struct packet_space *)
    ensures
      (exists* (psv: $type(struct packet_space)). pts_to ps #1.0R psv)
      ** pure (r == ps)
  {
    PS.struct_packet_space__back_container var_back
  }

  // Recovery from an inline-array field — the projection is the array *handle*
  // (no `ref` wrapper), and the container maps that handle back to the struct.
  fn get_from_data
      (#ps: $type(struct packet_space *))
      (var_data: (a: array $type(int32_t) { length a == 4 }))
    requires
      (exists* (psv: $type(struct packet_space)). pts_to ps #1.0R psv)
      ** pure (PS.struct_packet_space__data_1 ps == var_data)
    returns r: $type(struct packet_space *)
    ensures
      (exists* (psv: $type(struct packet_space)). pts_to ps #1.0R psv)
      ** pure (r == ps)
  {
    PS.struct_packet_space__data_container var_data
  }

  // A caller that owns the packet_space recovers a usable pointer and
  // re-attaches full ownership to it.
  fn client_uses_recovered_pointer
      (#ps: $type(struct packet_space *))
      (var_tracker: $type(ack_tracker_t *))
    requires
      (exists* (psv: $type(struct packet_space)). pts_to ps #1.0R psv)
      ** pure (PS.struct_packet_space__tracker_1 ps == var_tracker)
    returns r: $type(struct packet_space *)
    ensures
      exists* (psv: $type(struct packet_space)). pts_to r #1.0R psv
  {
    let r = get_from_tracker var_tracker;
    with psv. rewrite (pts_to ps #1.0R psv) as (pts_to r #1.0R psv);
    r
  }

  // --- Right-inverse (dual) lemmas: `proj (container r) == r`, one per field
  // kind. Each is discharged automatically by the generated
  // `..._proj_container_inv` SMTPat firing on the round-trip term. For a
  // translated-C function whose verification depends on this lemma, see
  // `test/container_field_read`. ---

  fn dual_tracker (var_tracker: $type(ack_tracker_t *))
    requires emp
    ensures pure (PS.struct_packet_space__tracker_1
                    (PS.struct_packet_space__tracker_container var_tracker) == var_tracker)
  { () }

  fn dual_id (var_id: $type(int32_t *))
    requires emp
    ensures pure (PS.struct_packet_space__id_1
                    (PS.struct_packet_space__id_container var_id) == var_id)
  { () }

  fn dual_back (var_back: $type(int32_t **))
    requires emp
    ensures pure (PS.struct_packet_space__back_1
                    (PS.struct_packet_space__back_container var_back) == var_back)
  { () }

  fn dual_data (var_data: (a: array $type(int32_t) { length a == 4 }))
    requires emp
    ensures pure (PS.struct_packet_space__data_1
                    (PS.struct_packet_space__data_container var_data) == var_data)
  { () }

  // Realistic frame-matcher use: owning the embedded field's cell *addressed
  // through the enclosing struct recovered by container_of* is the same as
  // owning it directly. Mirrors the msquic ack_tracker-inside-packet_space
  // case. The Pulse frame matcher does not fire the SMTPat on its own, so we
  // bridge with an explicit `rewrite` (whose ref-equality goal the
  // right-inverse SMTPat discharges) -- just as `client_uses_recovered_pointer`
  // does for the left-inverse. This rewrite does not typecheck without the
  // `..._proj_container_inv` lemma.
  fn readdress_tracker_cell (var_tracker: $type(ack_tracker_t *))
    requires
      (exists* (tv: $type(ack_tracker_t)).
         pts_to (PS.struct_packet_space__tracker_1
                   (PS.struct_packet_space__tracker_container var_tracker)) #1.0R tv)
    ensures
      (exists* (tv: $type(ack_tracker_t)). pts_to var_tracker #1.0R tv)
  {
    with tv. rewrite (pts_to (PS.struct_packet_space__tracker_1
                                (PS.struct_packet_space__tracker_container var_tracker)) #1.0R tv)
                  as (pts_to var_tracker #1.0R tv);
  }
)
