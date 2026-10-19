/*
 * Standalone case 4.1: C11 effective type (6.5p6) and strict aliasing (6.5p7).
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
 *   cc -std=c11 -O2 -Wall -Wextra case_4_1_change_effective_type_repeatedly.c -o case_4_1
 *   ./case_4_1
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
 * Case 16.1: An int store followed by a double read is invalid, and after a double store an int read is invalid instead.
 */

#include "annotations.h"
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>

#define BANNER(tag, title) \
    printf("\n== [%s] %s ==\n", tag, title)

/* A couple of plain aggregate types used throughout. */
struct point  { int x; int y; };

/* ================================================================== */
/* SECTION 4                                                          */
/* [DEFINED] No declared type -> the effective type may be CHANGED      */
/*           as many times as you like, by storing a new type.          */
/* ================================================================== */

static void case_4_1_change_effective_type_repeatedly(void)
{
    BANNER("DEFINED", "4.1: allocated storage re-typed over and over (R2 applied repeatedly)");

    /* One buffer, large & suitably aligned (malloc guarantees alignment for
       any type with a fundamental alignment, 7.22.3p1). */
    void *p = malloc(64);
    if (!p) return;

    *(int *)p = 7;                       /* effective type := int   */
    printf("   as int    : %d\n", *(int *)p);

    *(float *)p = 1.25f;                 /* effective type := float */
    printf("   as float  : %g\n", (double)*(float *)p);

    *(double *)p = 9.5;                  /* effective type := double */
    printf("   as double : %g\n", *(double *)p);

    *(struct point *)p = (struct point){ 1, 2 };  /* := struct point */
    printf("   as struct : {%d,%d}\n",
           ((struct point *)p)->x, ((struct point *)p)->y);

    *(long *)p = 123456789L;             /* effective type := long  */
    printf("   as long   : %ld\n", *(long *)p);

    /* Key point: each read above is paired with the store that *immediately*
       preceded it and installed that type.  No read ever looks back past a
       re-typing store.  That is what makes 4.1 defined and 16.1 (below) not. */
    free(p);
}

int main(void)
    _preserves(_live(stdout))
    _preserves_value(stdout)
{
    /* Unbuffered: if a UB case crashes, we still see how far we got. */
    setvbuf(stdout, NULL, _IONBF, 0);
    case_4_1_change_effective_type_repeatedly();
    return 0;
}
