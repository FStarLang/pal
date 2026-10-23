/*
 * Standalone case 24.8: C11 effective type (6.5p6) and strict aliasing (6.5p7).
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
 *   cc -std=c11 -O2 -Wall -Wextra case_24_8_punning_through_a_pointer_to_a_member.c -o case_24_8
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
 * Case 2.3: Reading a union member other than the one last stored reinterprets the stored bytes (6.5.2.3p3, footnote 95).
 * Case 24.1: A genuinely contested corner about what counts as an access through the union.
 */

#include "annotations.h"
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <stdint.h>

/* ------------------------------------------------------------------ */
/* Plumbing: opaque sinks so the optimizer cannot delete the accesses. */
/* ------------------------------------------------------------------ */

static volatile unsigned long long g_sink;

static void sink_u(unsigned long long v) { g_sink ^= v; }

#define BANNER(tag, title) \
    printf("\n== [%s] %s ==\n", tag, title)

union upun { float f; int32_t i; };

/* ================================================================== */
/* SECTION 24                                                          */
/* [UB] Union punning that does NOT work: the ways an object fails to   */
/*      actually acquire -- or fails to keep -- a union effective type. */
/* ================================================================== */

static void case_24_8_punning_through_a_pointer_to_a_member(void)
{
    BANNER("UB?", "24.8: the punning licence is for accesses THROUGH the union");

    /* The union is declared, so its effective type is `union upun` (R1) and
       2.3 reads `u.i` after storing `u.f`.  Here the read of the `int32_t`
       member goes through a plain `int32_t *` instead of the member access
       expression.  6.5.2.3p3 and footnote 95 speak of "the member used to
       read the contents of a union object", i.e. a `.`/`->` expression;
       `*pi` is not one, and the lvalue type `int32_t` is not the effective
       type of the `float` stored there.

       Honesty note: this is a genuinely contested corner.  GCC documents
       that type punning is only guaranteed through the union type itself and
       that this exact pattern "might not work" under -fstrict-aliasing;
       the committee has never settled it normatively.  Treated here as UB,
       consistently with 24.1. */
    union upun u;
    int32_t *pi = &u.i;
    u.f = 1.5f;
    printf("   *pi = 0x%08x   <-- UB?: not an access through the union\n",
           (unsigned)*pi);
    sink_u((unsigned)*pi);
}

int main(void)
    _preserves(_live(stdout))
    _preserves_value(stdout)
{
    /* Unbuffered: if a UB case crashes, we still see how far we got. */
    setvbuf(stdout, NULL, _IONBF, 0);
    case_24_8_punning_through_a_pointer_to_a_member();
    return 0;
}
