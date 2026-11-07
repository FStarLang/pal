/*
 * Standalone case 24.6: C11 effective type (6.5p6) and strict aliasing (6.5p7).
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
 *   cc -std=c11 -O2 -Wall -Wextra case_24_6_retyping_out_from_under_the_union.c -o case_24_6
 *   ./case_24_6
 *
 * This executable runs its case unconditionally, including any UB.
 * Compile with -O2 (not -fno-strict-aliasing) to allow aliasing optimizations.
 * "It printed the right number" proves nothing about undefined behavior.
 * GCC/Clang warnings on UB cases are expected (-Warray-bounds,
 * -Wmaybe-uninitialized, -Wstrict-aliasing); running UB cases may crash.
 * Additional diagnostic builds can use -Wstrict-aliasing=2 -fstrict-aliasing
 * or -O1 -g -fsanitize=undefined,address; sanitizers do not detect all UB.
 */

/* Historical observation in the combined corpus on x86-64 GCC 13 at -O2;
 * not a required result for this standalone program:
 *   24.6 still reports the old union payload after a `double` was stored
 *   over it: the union effective type is exactly as fragile as any other.
 */

/* Local context for cross-case references in the original comments:
 * Case 12.1: Assigning *u as a whole union installs the union effective type in allocated storage before member punning.
 * Case 12.5: Whole-union and double stores alternately retype allocated storage; each read follows the store that installed its own type.
 */

#include "annotations.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <stddef.h>

/* ------------------------------------------------------------------ */
/* Plumbing: opaque sinks so the optimizer cannot delete the accesses. */
/* ------------------------------------------------------------------ */

static volatile unsigned long long g_sink;

static void sink_u(unsigned long long v) { g_sink ^= v; }

#define BANNER(tag, title) \
    printf("\n== [%s] %s ==\n", tag, title)

union upun {
    int32_t  i;
    float    f;
    uint8_t  b[4];
};
_Static_assert(sizeof(float) == 4 && sizeof(int32_t) == 4,
               "section 12 assumes 32-bit float and int32_t");

/* ================================================================== */
/* SECTION 24                                                          */
/* [UB] Union punning that does NOT work: the ways an object fails to   */
/*      actually acquire -- or fails to keep -- a union effective type. */
/* ================================================================== */

static void case_24_6_retyping_out_from_under_the_union(void)
{
    BANNER("UB", "24.6: a non-member store destroys the union effective type (16.x meets unions)");

    void *p = malloc(sizeof(union upun) > sizeof(double)
                     ? sizeof(union upun) : sizeof(double));
    if (!p) return;

    union upun *u = p;
    *u = (union upun){ .f = 1.5f };   /* effective type := union upun */
    sink_u((unsigned)u->i);           /* legal union punning (12.1)   */

    *(double *)p = 2.5;               /* R2 again: effective type := double.
                                         The union object is gone; `u` is
                                         now a stale pointer of the old type. */

    printf("   u->i after a double store = %#" PRIx32 "   <-- UB\n", (uint32_t)u->i);
    sink_u((unsigned)u->i);

    /* Contrast 12.5, where every read followed the store that installed its
       own type.  A union effective type is exactly as fragile as any other. */
    free(p);
}

int main(void)
    _preserves(_live(stdout))
    _preserves_value(stdout)
{
    /* Unbuffered: if a UB case crashes, we still see how far we got. */
    setvbuf(stdout, NULL, _IONBF, 0);
    case_24_6_retyping_out_from_under_the_union();
    return 0;
}
