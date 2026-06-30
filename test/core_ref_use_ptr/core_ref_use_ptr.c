// Test: executable use of a `_core_ref` back-pointer when the embedding struct
// holds its inner struct through a POINTER (the pointer-embed counterpart of
// test/core_ref_use, which embeds the inner struct by value).
//
// As in core_ref_use, `struct inner` holds a `_core_ref` back-pointer to the
// `struct bar` it belongs to, and using that back-pointer in executable code
// means converting between the untyped `core_ref` it is stored as and a typed
// `ref bar` (PAL inserts `core_to_ref`/`ref_to_core` coercions). The difference
// here is that `struct bar` reaches its `inner` via `struct inner *myinner`
// rather than by value, so recovering the back-pointer additionally goes
// through a real pointer field read on `bar`.
//
// This is the construct in MsQuic's QuicAckTrackerOnAckFrameAcked, where the
// `_core_ref` `Connection` back-pointer is later dereferenced as a typed pointer.

#include "pal.h"

struct bar;

struct inner {
    int *a;                     // owned field -> inner has a real predicate
    _core_ref struct bar *back; // untyped back-pointer (breaks the cycle)
};

struct bar {
    long *other;                // owned field -> bar has a real predicate
    struct inner *myinner;      // pointer embed -> bar/inner are cyclic via a ptr
};

/* Read direction (core_to_ref): reach the inner through the pointer field
 * `b->myinner`, recover its back-pointer as a typed `ref bar`, and dereference
 * one of that bar's fields. The caller hands over ownership of the bar reached
 * through `back`; a `_core_ref` carries none by design, so this clause cannot be
 * auto-generated and is supplied (and preserved) by hand. */
void via_inner(struct bar *b)
  _requires(_inline_pulse(
    exists* (bv: $type(struct bar)).
      pts_to (Pulse.Lib.C.CoreRef.core_to_ref $type(struct bar)
                ($(*(b->myinner))).$field(struct inner::back)) bv))
  _ensures(_inline_pulse(
    exists* (bv: $type(struct bar)).
      pts_to (Pulse.Lib.C.CoreRef.core_to_ref $type(struct bar)
                ($(*(b->myinner))).$field(struct inner::back)) bv))
{
    struct inner *p = b->myinner; // pointer-embed field read on bar
    struct bar *b2 = p->back;     // core_to_ref coercion emitted here
    long *o = b2->other;          // executable field read through the typed pointer
}

/* Write direction (ref_to_core): store a typed `ref bar` into a `core_ref`
 * slot. Ownership of `b` is untouched, so the auto-generated spec suffices. */
void store(struct bar *b) {
    _core_ref struct bar *c = b; // ref_to_core coercion emitted here
}
