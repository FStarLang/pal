/*
 * Standalone case 4.2: C11 effective type (6.5p6) and strict aliasing (6.5p7).
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
 *   cc -std=c11 -O2 -Wall -Wextra case_4_2_retype_after_free_and_realloc.c -o case_4_2
 *   ./case_4_2
 *
 * This executable runs its case unconditionally, including any UB.
 * Compile with -O2 (not -fno-strict-aliasing) to allow aliasing optimizations.
 * "It printed the right number" proves nothing about undefined behavior.
 * GCC/Clang warnings on UB cases are expected (-Warray-bounds,
 * -Wmaybe-uninitialized, -Wstrict-aliasing); running UB cases may crash.
 * Additional diagnostic builds can use -Wstrict-aliasing=2 -fstrict-aliasing
 * or -O1 -g -fsanitize=undefined,address; sanitizers do not detect all UB.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>

#define BANNER(tag, title) \
    printf("\n== [%s] %s ==\n", tag, title)

/* ================================================================== */
/* SECTION 4                                                          */
/* [DEFINED] No declared type -> the effective type may be CHANGED      */
/*           as many times as you like, by storing a new type.          */
/* ================================================================== */

static void case_4_2_retype_after_free_and_realloc(void)
{
    BANNER("DEFINED", "4.2: realloc'd storage still has no declared type, so re-typing is fine");

    void *p = malloc(sizeof(int) * 4);
    if (!p) return;
    for (int i = 0; i < 4; i++)
        ((int *)p)[i] = i;               /* effective types := int */

    void *q = realloc(p, sizeof(double) * 4);
    if (!q) { free(p); return; }
    /* realloc copies the old bytes "as if" by memcpy, so by R3 the first
       chunk still has effective type int -- reading it as int is fine... */
    printf("   preserved ints: %d %d\n", ((int *)q)[0], ((int *)q)[1]);
    /* ...and because q still has no *declared* type, a fresh store re-types
       it (R2). */
    for (int i = 0; i < 4; i++)
        ((double *)q)[i] = i * 0.5;
    printf("   now doubles  : %g %g\n", ((double *)q)[0], ((double *)q)[3]);
    free(q);
}

int main(void)
{
    /* Unbuffered: if a UB case crashes, we still see how far we got. */
    setvbuf(stdout, NULL, _IONBF, 0);
    case_4_2_retype_after_free_and_realloc();
    return 0;
}
