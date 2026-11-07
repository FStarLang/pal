// Test: a callee writes a pointer into the caller's own slot through an
// untyped out-parameter -- the `f((void const ** )&typedLocal)` idiom that
// every "acquire a buffer" interface is spelled with.
//
// Under Palow every pointer is a `ptr`, so the caller's `struct hdr const *`
// slot and the callee's `void const *` slot are the same object at the same
// type: the cast changes nothing about the storage, and the argument is the
// slot's address, handed over as an `_out` like any other. The slot has just
// been set to NULL rather than left uninitialized, so its value is given up on
// the way in, as for any written local passed to an `_out`.
//
// What the acquired buffer *means* is not something PAL can invent: the callee
// returns an address and only its contract says what may be read there. That
// is written by hand as an `_ensures` naming the points-to at the address the
// callee stored. Being ownership, it states the slot as well, since it
// replaces the `_out`'s own. Without it the dereference below is rejected.

#include "pal.h"
#include <stddef.h>

struct hdr {
    int a;
    int b;
};

typedef void const* PAL_RAW_CPTR;

/* Hands back a buffer at an erased type. The `_ensures` is the licence to read
 * it as a `struct hdr`; nothing in the C types says so. */
int acquire(unsigned n, _out PAL_RAW_CPTR* buf)
  _ensures(_inline_pulse(
    exists* (q: ptr) (hv: $type(struct hdr)).
      ptr_pts_to $(buf) 1.0R q **
      Struct_hdr.struct_hdr_pts_to q 1.0R hv));

/* Releases it again, taking the licence back, so nothing is left over. */
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
