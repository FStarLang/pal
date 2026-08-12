// Test: a callee writes a pointer into the caller's own slot through an
// untyped out-parameter -- the `f((void const ** )&typedLocal)` idiom that
// every "acquire a buffer" interface is spelled with.
//
// This exercises the *cell* view shift, not the pointer coercion. `_core_ref`
// on the pointee of the out-parameter makes the slot a `ref core_ref`, while
// the caller's local is a `ref (ref hdr)`. Those are the same location holding
// the same machine word, but different F* types, so PAL emits
// `core_cell` on the argument and walks the ownership across with
// `to_core_cell_out` before the call and `of_core_cell` after -- an
// out-parameter goes in empty and comes back full, so the two halves differ.
//
// What the acquired buffer *means* is not something PAL can invent: the callee
// returns an address and only its contract says what may be read there. That
// is written by hand as an `_ensures` in terms of `core_to_ref`, which is the
// slprop that licenses the cast. Without it the dereference below is rejected.

#include "pal.h"
#include <stddef.h>

struct hdr {
    int a;
    int b;
};

typedef _core_ref void const* PAL_RAW_CPTR;

/* Hands back a buffer at an erased type. The `_ensures` is the licence to read
 * it as a `struct hdr`; nothing in the C types says so. */
int acquire(unsigned n, _out PAL_RAW_CPTR* buf)
  _ensures(_inline_pulse(
    exists* (hv: $type(struct hdr)).
      pts_to (Pulse.Lib.C.CoreRef.core_to_ref $type(struct hdr) ($(*buf))) hv));

/* Releases it again, taking the licence back, so nothing is left over. It
 * takes the typed pointer the caller recovered: by this point the cast has
 * been licensed and there is nothing left to erase. */
void release(_consumes struct hdr const* h);

int use(void)
{
    struct hdr const* h = NULL;
    struct hdr out;

    int s = acquire(sizeof(struct hdr), (void const**)&h);
    out = *h;                 // read through the pointer the callee wrote
    release(h);
    return out.a;
}
