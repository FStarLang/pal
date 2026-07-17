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
// reachable through `node` is required and handed back, named in the spec with
// the same `_container_of(node, struct outer, node)` intrinsic used in the body
// (so no generated symbol has to be spelled by hand, and no separate linkage
// fact is needed). The postconditions also state the *functional* effect: after
// `set_value_via_node` the recovered parent's `value` is `v`, and
// `read_value_via_node` returns the parent's current `value`.

#include <assert.h>
#include <stdint.h>
#include "pal.h"

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
        pts_to $(_container_of(node, struct outer, node)) #1.0R ov **
        Struct_outer.struct_outer__pred
          (!$(_container_of(node, struct outer, node))) 1.0R))
    _ensures(_inline_pulse(
      exists* (ov: $type(struct outer)).
        pts_to $(_container_of(node, struct outer, node)) #1.0R ov **
        Struct_outer.struct_outer__pred
          (!$(_container_of(node, struct outer, node))) 1.0R **
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
        pts_to $(_container_of(node, struct outer, node)) #1.0R ov **
        Struct_outer.struct_outer__pred
          (!$(_container_of(node, struct outer, node))) 1.0R))
    _ensures(_inline_pulse(
      pure ($(return) ==
        !(Struct_outer.struct_outer__get_value
            $(_container_of(node, struct outer, node))))))
{
    struct outer *parent = _container_of(node, struct outer, node);
    return parent->value;
}

// ---------------------------------------------------------------------------
// Offset-0 `container_of` null preservation, written in plain C.
//
// `struct outer`'s first member `value` sits at offset 0, so recovering the
// enclosing `outer` from a `&outer->value` pointer — or projecting back down to
// that field — is pointer identity (C 6.7.2.1: no leading padding). PAL lowers a
// first-field pointer cast to exactly this recovery: `(struct outer *)fieldptr`
// becomes the generated `struct_outer__value_container` map, and `(int32_t *)
// nodeptr` becomes the field projection `struct_outer__value_1`.
//
// This idiom is pervasive in MsQuic, where CXPLAT_CONTAINING_RECORD walks
// intrusive lists whose link sits at offset 0 and whose NULL `next` terminates
// the walk: the recovery MUST preserve NULL, or the terminator could never be
// detected. That termination fact is the emitted `struct_outer__value_proj_null`
// axiom (`proj(NULL) == NULL`). Its dual, `container(NULL) == NULL`, is not
// emitted separately — it follows from `struct_outer__value_container_inv` at
// `p = NULL` rewritten with `proj_null` — which is why the container-direction
// assertion below still verifies with only the one axiom.

// Projection direction: `(int32_t *)y` takes the address of the offset-0 field.
// On NULL this is `proj(NULL) == NULL` — the emitted axiom, and the fact that
// gives this assertion its teeth (remove the axiom and this stops verifying).
void value_proj_null_fires(void) {
    int32_t *x = 0;
    struct outer *y = 0;
    assert(x == (int32_t *)y);
}

// Container direction: `(struct outer *)x` recovers the enclosing node from a
// pointer to its offset-0 field. On NULL this is `container(NULL) == NULL`,
// derived from `proj_null` and `struct_outer__value_container_inv`.
void value_container_null_fires(void) {
    int32_t *x = 0;
    struct outer *y = 0;
    assert((struct outer *)x == y);
}
