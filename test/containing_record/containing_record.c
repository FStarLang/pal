// Test: the CONTAINING_RECORD / offsetof idiom, performed in *translated C*.
//
// This mirrors intrusive-container code such as MsQuic's
// QuicAckTrackerOnAckFrameAcked, which receives a pointer to an *embedded*
// field and recovers the enclosing object with
//   CXPLAT_CONTAINING_RECORD(fieldptr, QUIC_PACKET_SPACE, AckTracker)
//     == (QUIC_PACKET_SPACE *)((char *)fieldptr - offsetof(...))
// before touching the parent's other fields.
//
// PAL exposes this as the `_container_of(ptr, type, field)` intrinsic, which
// lowers to the generated per-field `struct_<T>__<field>_container` function
// (the exact pointer adjustment, with a left-inverse lemma). Here the recovery
// runs entirely inside the C body — no hand-written Pulse — and only the
// ownership contract is stated in spec syntax.
//
// `set_value_via_node` / `read_value_via_node` take a pointer to the embedded
// `node` field, recover the enclosing `outer` with `_container_of`, and then
// write / read the sibling `value` field. Ownership of the whole `outer`
// reachable through `node` is required and handed back, named with the same
// `struct_outer__node_container` term the intrinsic emits (so no separate
// linkage fact is needed). The postconditions also state the *functional*
// effect: after `set_value_via_node` the recovered parent's `value` is `v`, and
// `read_value_via_node` returns the parent's current `value`.

#include "pal.h"
#include <stdint.h>

struct inner {
    int32_t marker;
};

struct outer {
    int32_t value;      // the sibling field, written / read via the recovered parent
    struct inner node;  // the embedded field callers hold a pointer to (nonzero offset)
};

// offsetof write: recover `outer` from `&outer->node` and set `outer->value`.
void set_value_via_node(_plain struct inner *node, int32_t v)
    _requires(_inline_pulse(
      exists* (ov: $type(struct outer)).
        pts_to (Struct_outer.struct_outer__node_container $(node)) #1.0R ov **
        Struct_outer.struct_outer__pred
          (!(Struct_outer.struct_outer__node_container $(node))) 1.0R))
    _ensures(_inline_pulse(
      exists* (ov: $type(struct outer)).
        pts_to (Struct_outer.struct_outer__node_container $(node)) #1.0R ov **
        Struct_outer.struct_outer__pred
          (!(Struct_outer.struct_outer__node_container $(node))) 1.0R **
        pure (ov.Struct_outer.struct_outer__value == $(v))))
{
    struct outer *parent = _container_of(node, struct outer, node);
    parent->value = v;
}

// offsetof read: recover `outer` from `&outer->node` and read `outer->value`.
// Ownership is unchanged across the call, so the shared predicate is stated once
// with `_preserves`; only the functional result is `_ensures`-only.
int32_t read_value_via_node(_plain struct inner *node)
    _preserves(_inline_pulse(
      exists* (ov: $type(struct outer)).
        pts_to (Struct_outer.struct_outer__node_container $(node)) #1.0R ov **
        Struct_outer.struct_outer__pred
          (!(Struct_outer.struct_outer__node_container $(node))) 1.0R))
    _ensures(_inline_pulse(
      pure ($(return) ==
        !(Struct_outer.struct_outer__get_value
            (Struct_outer.struct_outer__node_container $(node))))))
{
    struct outer *parent = _container_of(node, struct outer, node);
    return parent->value;
}
