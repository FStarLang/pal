// Test: executable use of a `_core_ref` back-pointer as a typed pointer.
//
// `struct inner` holds a `_core_ref` back-pointer to the `struct bar` that
// embeds it (a cyclic pair, like test/core_ref_struct). Using the back-pointer
// in real code means converting between the untyped `core_ref` it is stored as
// and a typed `ref bar`; PAL inserts `core_to_ref`/`ref_to_core` coercions for
// this. `core_ref_struct` only recovers the back-pointer in ghost/spec code and
// null-tests it; here it is read and written in executable code.
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
    struct inner myinner;       // by-value embed -> bar/inner are cyclic
};

/* Read direction (core_to_ref): recover the back-pointer as a typed `ref bar`
 * and dereference one of its fields. The caller hands over ownership of the bar
 * reached through `back`; a `_core_ref` carries none by design, so this single
 * clause cannot be auto-generated and is supplied (and preserved) by hand. */
void via_back(struct inner *p)
  _requires(_inline_pulse(
    exists* (bv: $type(struct bar)).
      pts_to (Pulse.Lib.C.CoreRef.core_to_ref $type(struct bar)
                ($(*p)).$field(struct inner::back)) bv))
  _ensures(_inline_pulse(
    exists* (bv: $type(struct bar)).
      pts_to (Pulse.Lib.C.CoreRef.core_to_ref $type(struct bar)
                ($(*p)).$field(struct inner::back)) bv))
{
    struct bar *b = p->back; // core_to_ref coercion emitted here
    long *o = b->other;      // executable field read through the typed pointer
}

/* Write direction (ref_to_core): store a typed `ref bar` into a `core_ref`
 * slot. Ownership of `b` is untouched, so the auto-generated spec suffices. */
void store(struct bar *b) {
    _core_ref struct bar *c = b; // ref_to_core coercion emitted here
}
