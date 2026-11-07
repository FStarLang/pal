/*
 * Standalone case 24.10: C11 effective type (6.5p6) and strict aliasing (6.5p7).
 *
 * Reference (N1570, the public C11 committee draft):
 *   https://port70.net/~nsz/c/c11/n1570.html#6.5p6
 *   https://www.open-std.org/jtc1/sc22/wg14/docs/n1570.pdf   (6.5p6, p. 83)
 *
 * ---------------------------------------------------------------------------
 * 6.5p6 states four rules.  Paraphrased:
 *
 *   (R1) If the object has a DECLARED type, the effective type for every
 *        access is that declared type.  It can never change.
 *
 *   (R2) If the object has NO declared type (i.e. allocated storage) and a
 *        value is stored into it through an lvalue whose type is NOT a
 *        character type, then that lvalue's type BECOMES the effective type,
 *        for that access and for all subsequent *non-modifying* accesses.
 *
 *   (R3) If the object has NO declared type and a value is copied into it with
 *        memcpy/memmove, or is copied as an array of character type, then the
 *        effective type becomes the effective type of the SOURCE object,
 *        "if it has one".
 *
 *   (R4) For all other accesses to an object with no declared type, the
 *        effective type is simply the type of the lvalue used for the access.
 *        (This is the fallback: untouched malloc'd bytes have no sticky type,
 *        so any lvalue type is permissible as far as 6.5p7 is concerned.)
 *
 * 6.5p7 then says: an object's stored value may only be accessed by an lvalue
 * whose type is
 *      - compatible with the effective type,
 *      - a qualified version of it,
 *      - the signed/unsigned counterpart of it (or of a qualified version),
 *      - an aggregate or union type containing one of the above among its
 *        members (including, recursively, members of subaggregates), or
 *      - a character type.
 * Anything else is undefined behavior.
 *
 *
 * The case's banner uses these tags:
 *     [DEFINED]  strictly conforming
 *     [UB]       undefined behavior, per the cited rule
 *     [UNSPEC]   defined as far as 6.5p6/p7 go, but another rule bites
 *     [IMPL-DEF] the implementation chooses, and may choose badly
 *     [UB?]      a genuinely contested corner; see the case's own note
 *
 * Build and run from this file's directory:
 *   cc -std=c11 -O2 -Wall -Wextra case_24_10_common_initial_sequence_needs_the_union_visible.c -o case_24_10
 *   ./case_24_4
 *
 * This executable runs its case unconditionally, including any UB.
 * Compile with -O2 (not -fno-strict-aliasing) to allow aliasing optimizations.
 * "It printed the right number" proves nothing about undefined behavior.
 * GCC/Clang warnings on UB cases are expected (-Warray-bounds,
 * -Wmaybe-uninitialized, -Wstrict-aliasing); running UB cases may crash.
 * Additional diagnostic builds can use -Wstrict-aliasing=2 -fstrict-aliasing
 * or -O1 -g -fsanitize=undefined,address; sanitizers do not detect all UB.
 */

/* Local context for cross-case references in the original comments:
 * Case 8.1: A declared union containing structs with a common initial sequence permits inspecting that common part through either struct member.
 */

#include "annotations.h"
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>

/* ------------------------------------------------------------------ */
/* Plumbing: opaque sinks so the optimizer cannot delete the accesses. */
/* ------------------------------------------------------------------ */

static volatile unsigned long long g_sink;

static void sink_u(unsigned long long v) { g_sink ^= v; }

#define BANNER(tag, title) \
    printf("\n== [%s] %s ==\n", tag, title)

struct cis_a { int tag; int x; };
struct cis_b { int tag; double y; };

/* The union's declaration is NOT visible here: it is declared below. */
static int read_tag(struct cis_a *pa)
    _requires(_live(*pa))
    _ensures(_live(*pa))
{
    return pa->tag;
}

union  cis   { struct cis_a a; struct cis_b b; };

/* ================================================================== */
/* SECTION 24                                                          */
/* [UB] Union punning that does NOT work: the ways an object fails to   */
/*      actually acquire -- or fails to keep -- a union effective type. */
/* ================================================================== */

static void case_24_10_common_initial_sequence_needs_the_union_visible(void)
{
    BANNER("UB", "24.10: the common initial sequence licence needs the union in view");

    /* 6.5.2.3p6 permits inspecting the common initial part "anywhere that a
       declaration of the completed type of the union is visible".  `read_tag`
       is defined before `union cis` is declared, so inside it the licence
       does not apply: `pa->tag` is an access to a `struct cis_b` object
       through an lvalue of a member of `struct cis_a`, an unrelated struct
       type, exactly as in 13.3.  Compilers rely on this: without the union
       in sight, `struct cis_a *` and `struct cis_b *` are assumed not to
       alias. */
    union cis u;
    u.b.tag = 7;
    u.b.y   = 1.5;
    int t = read_tag(&u.a);
    printf("   read_tag(&u.a) = %d   <-- UB: no union declaration visible in read_tag\n", t);
    sink_u((unsigned)t);
}

int main(void)
    _preserves(_live(stdout))
    _preserves_value(stdout)
{
    /* Unbuffered: if a UB case crashes, we still see how far we got. */
    setvbuf(stdout, NULL, _IONBF, 0);
    case_24_10_common_initial_sequence_needs_the_union_visible();
    return 0;
}
