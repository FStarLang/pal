// Test: casts between a pointer and its numeric address.
//
// Before this was supported, `(uint64_t)p` and `(T *)n` fell through to
// "unsupported rvalue expression CStyleCastExpr". That is worse than a missing
// feature: PAL emits `(admit())` for the enclosing expression, so the rest of
// the function's obligations stop being checked too. In one real code base 21
// of 25 untranslated functions were this one construct.
//
// Both directions go through `core_ref`, PAL's raw-pointer model, and both
// primitives are UNINTERPRETED:
//
//   - pointer -> integer is sound outright. Reading an address tells a program
//     nothing about memory and costs it nothing; the pointer is unaffected.
//   - integer -> pointer produces a pointer carrying NO ownership. Nothing can
//     be read or written through it. "Address A holds an object of type T" is
//     a fact about a linker script, not about the C, so it cannot be proved
//     here and has to be assumed where it is claimed.
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

/* Pointer to integer, the width the address natively has. */
uint64_t addr_of(struct node *p)
{
    return (uint64_t) p;
}

/* Narrowing. C truncates, and so does the translation -- this must NOT become
 * a proof obligation that the address fits in 32 bits. */
uint32_t addr_lo(struct node *p)
{
    return (uint32_t) (uint64_t) p;
}

/* Through a signed type, which is what `intptr_t` expands to. */
int64_t addr_signed(struct node *p)
{
    return (int64_t) p;
}

/* A different pointee, and a void pointer: the address primitive is
 * non-parametric, so neither needs its own case. */
uint64_t addr_of_int(int *p)
{
    return (uint64_t) p;
}

uint64_t addr_of_void(void *p)
{
    return (uint64_t) p;
}

/* Taking an address does not consume the pointer: the caller still owns the
 * pointee afterwards. If `core_ref_to_u64` were modelled as anything other
 * than a pure function of the pointer, this would fail. */
int addr_then_read(struct node *p)
{
    uint64_t a = (uint64_t) p;
    if (a == 0) {
        return 0;
    }
    return p->tag;
}

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
 *           : Lemma (u64_to_core_ref (core_ref_to_u64 r) == r) = ()
 *
 *     against Pulse.Lib.C.CoreRef gives, as required, `Error 19`. If this
 *     ever succeeds, someone has added a round-trip law, and `round_trip`
 *     above stops being the no-op it is documented to be.
 */
int falsifications_are_documented_above(void)
{
    return 0;
}
