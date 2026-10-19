/*
 * Standalone case 21.1: C11 effective type (6.5p6) and strict aliasing (6.5p7).
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
 *   cc -std=c11 -O2 -Wall -Wextra case_21_1_restrict_violation_with_matching_types.c -o case_21_1
 *   ./case_21_1
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
 *   21.1 returns 1 although memory holds 2: `restrict` let the compiler keep
 *   the stale value, with no type mismatch anywhere in sight.
 */

#include "annotations.h"
#include <stdio.h>
#include <stdint.h>
#include <stddef.h>

/* ------------------------------------------------------------------ */
/* Plumbing: opaque sinks so the optimizer cannot delete the accesses. */
/* ------------------------------------------------------------------ */

static volatile unsigned long long g_sink;

static void sink_u(unsigned long long v) { g_sink ^= v; }

static void sink_p(_plain const void *v)        { g_sink ^= (unsigned long long)(uintptr_t)v; }

/* An "opaque" identity for pointers: defeats constant propagation without
   itself being UB. */
static _plain void *opaque(_plain void *p)
    _ensures(return == p)
{ sink_p(p); return p; }

static int case_21_helper(int *restrict a, int *restrict b)
    _ensures(*a == 1 && *b == 2 && return == 1)
{
    *a = 1;
    *b = 2;      /* the programmer has promised `b` does not alias `a` */
    return *a;   /* the compiler may fold this to 1 */
}

#define BANNER(tag, title) \
    printf("\n== [%s] %s ==\n", tag, title)

/* ================================================================== */
/* SECTION 21                                                         */
/* [UB] Effective types agree PERFECTLY and the access is still UB,     */
/*      because `restrict` is an orthogonal promise (6.7.3.1).          */
/* ================================================================== */

static void case_21_1_restrict_violation_with_matching_types(void)
{
    BANNER("UB", "21.1: identical effective types, but a `restrict` promise is broken");

    int x = 0;
    int *p = opaque(&x);
    int r = case_21_helper(p, p);     /* UB: both parameters are restrict-qualified
                                   and designate the same object, yet both are
                                   used to modify it.  6.5p6/p7 are entirely
                                   satisfied -- the effective type is `int` on
                                   every access.  Aliasing UB is not only
                                   about types. */
    printf("   returned %d (compiler may say 1, memory says 2)   <-- UB\n", r);
    sink_u((unsigned)r);
}

int main(void)
    _preserves(_live(stdout))
    _preserves_value(stdout)
{
    /* Unbuffered: if a UB case crashes, we still see how far we got. */
    setvbuf(stdout, NULL, _IONBF, 0);
    case_21_1_restrict_violation_with_matching_types();
    return 0;
}
