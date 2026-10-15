// Test: integer-to-pointer casts, `(T *)n`.
//
// Before this was supported, `(T *)n` fell through to "unsupported rvalue
// expression CStyleCastExpr". That is worse than a missing feature: PAL emits
// `(admit())` for the enclosing expression, so the rest of the function's
// obligations stop being checked too.
//
// The cast goes through `core_ref`, PAL's raw-pointer model, via the
// UNINTERPRETED `u64_to_core_ref`, and produces a pointer carrying NO
// ownership. Nothing can be read or written through it. "Address A holds an
// object of type T" is a fact about a linker script, not about the C, so it
// cannot be proved here and has to be assumed where it is claimed.
//
// The pointer-to-integer direction is test/pointer_integer_cast.
//
// The last two functions are the ones that matter: they pin that an address
// obtained from an integer grants nothing, by showing the surrounding code
// still verifies while the manufactured pointer stays unusable.

#include "pal.h"
#include <stdint.h>
#include <stddef.h>

struct node {
    int tag;
    int payload;
};

/* Integer to pointer. The result is `_plain` -- it carries no ownership, and
 * saying so is the honest signature. */
_plain struct node *at_address(uint64_t addr)
{
    return (struct node *) addr;
}

/* The round trip is NOT the identity, deliberately: C guarantees it only
 * through `uintptr_t`, and PAL does not model pointer provenance. This exists
 * to be translated, not to prove anything about the result. */
_plain struct node *round_trip(struct node *p)
{
    return (struct node *) (uint64_t) p;
}

/* A narrower integer widens first, exactly as C says. */
_plain struct node *at_address32(uint32_t addr)
{
    return (struct node *) (uint64_t) addr;
}

/* THE POINT OF THE TEST, part 1: a function that manufactures an address and
 * then does real work on memory it genuinely owns still verifies. Had the cast
 * disturbed ownership, this would break. */
int use_address_and_own(struct node *p, uint64_t addr)
{
    struct node *q = (struct node *) addr;
    if (q == NULL) {
        return 0;
    }
    p->tag = 1;
    return p->tag;
}

/* THE POINT OF THE TEST, part 2: the two things that must NOT be provable.
 *
 * A suite that must pass cannot contain a case that must fail, so both were
 * run by hand and their exact errors recorded here. Re-run them if either
 * primitive is ever given a definition or an axiom.
 *
 * (a) The manufactured pointer is unusable -- there is no `pts_to` for an
 *     address that came out of an integer, and the translation invents none.
 *     Appending
 *
 *         int FALSIFY_read_unowned(uint64_t addr)
 *         {
 *             struct node *q = (struct node *) addr;
 *             return q->tag;
 *         }
 *
 *     gives, as required:
 *
 *         Error 228 ... Tactic failed - Cannot prove:
 *           Struct_node.struct_node__aux_raw_unfolded
 *             (core_to_ref Struct_node.struct_node (u64_to_core_ref var_addr))
 *
 * (b) The round trip is not the identity. Checking
 *
 *         let rt (r: core_ref)
 *           : Lemma (u64_to_core_ref (core_to_uint64 r) == r) = ()
 *
 *     against Pulse.Lib.C.CoreRef gives, as required, `Error 19`. If this
 *     ever succeeds, someone has added a round-trip law, and `round_trip`
 *     above stops being the no-op it is documented to be.
 */
int falsifications_are_documented_above(void)
{
    return 0;
}

/* A fixed array decaying straight to a raw pointer, which is what `(void *)a`
 * does. Both steps are the identity in Pulse -- take the array's handle as a
 * `ref`, then erase its pointee type -- so the result is the base address
 * carrying no ownership and no length. That is the honest model of a `void *`:
 * there is no pointee type left to own, so nothing can be read through it.
 *
 * This sits here rather than in its own test because it is the same erasure to
 * `core_ref` that the address primitive above is built on; before it was
 * handled the cast reported "unsupported cast from uint8_t[65536] to
 * void*[core]" and took its whole function's proof down with it.
 */
struct blobholder {
    uint8_t blob[64];
};

void *blob_as_void(struct blobholder *h)
{
    return h->blob;
}

/* The caller keeps its ownership across the decay: `h` is still fully owned on
 * return, which the generated `ensures` states and the body has to re-establish. */
uint8_t blob_decay_then_read(struct blobholder *h)
{
    void *raw = h->blob;
    if (raw == NULL) {
        return 0;
    }
    return h->blob[0];
}

/* The decayed address of an array field of a live object is not NULL.
 * `array_pts_to_not_null` puts `not (array_is_null a)` in context, and
 * `array_to_ref_is_null` carries it across the `array_to_ref` step of the
 * decay, and `ref_to_core_is_null` carries it to the `core_ref`. Without
 * `array_to_ref_is_null` the postcondition does not verify. */
void *blob_addr(struct blobholder *h)
    _ensures(return != NULL)
{
    void *raw = h->blob;
    /* The same fact in Palow, where the decay is the identity on addresses:
       the field has to be focused for its bytes to be in hand, and owning a
       byte is what rules out the empty provenance. */
    _ghost_stmt(Struct_blobholder.struct_blobholder_focus_blob $(h));
    _ghost_stmt(Pulse.Lib.C.Palow.Array.array_pts_to_not_null uint8_t_repr 1
        (FStar.SizeT.v uint8_t_alignof)
        ($(h) +! Struct_blobholder.struct_blobholder_offsetof_blob));
    _ghost_stmt(Struct_blobholder.struct_blobholder_unfocus_read_blob $(h));
    return raw;
}
