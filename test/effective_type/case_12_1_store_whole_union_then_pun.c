/*
 * Standalone case 12.1: C11 effective type (6.5p6) and strict aliasing (6.5p7).
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
 *   cc -std=c11 -O2 -Wall -Wextra case_12_1_store_whole_union_then_pun.c -o case_12_1
 *   ./case_12_1
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
 * Case 2.3: A declared union permits member punning; the resulting value can be unspecified or a trap representation.
 * Case 24.1: Whether a union-member store in allocated storage installs only the member type or establishes a union is contested; a whole-union store avoids that question.
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
/* SECTION 12                                                          */
/* [DEFINED] The effective type is set to a UNION type, and the object  */
/*           is then type-punned through that union.                    */
/*                                                                      */
/*           This is the one place where R2 and 6.5.2.3 cooperate: once  */
/*           allocated storage has acquired a union effective type, the  */
/*           object really IS a union, so footnote 95's "the bytes are   */
/*           reinterpreted" licence applies exactly as it would to a     */
/*           declared union (cf. 2.3).  The access is legal; only the    */
/*           resulting VALUE is unspecified.                             */
/* ================================================================== */

static void case_12_1_store_whole_union_then_pun(void)
{
    BANNER("DEFINED", "12.1: storing a WHOLE union into malloc'd storage installs the union type");

    union upun *u = malloc(sizeof *u);
    if (!u) return;

    /* The lvalue being assigned is `*u`, whose type is `union upun`, and the
       object has no declared type -- so R2 installs `union upun` as the
       effective type of those 4 bytes.  Note the whole-union store: that is
       what makes this case work (contrast 24.1). */
    *u = (union upun){ .f = 1.5f };

    /* The object's effective type is now a union type, so reading a member
       other than the one last stored is ordinary union punning (6.5.2.3p3 and
       footnote 95), not an aliasing violation. */
    printf("   stored .f=1.5f, read .i = %#" PRIx32 "   (value unspecified, access legal)\n",
           (uint32_t)u->i);
    sink_u((unsigned)u->i);

    /* The uint8_t member is doubly safe: it is both a member of the union AND
       a character type, so 6.5p7's final bullet covers it unconditionally. */
    printf("   bytes = %02x %02x %02x %02x\n", u->b[0], u->b[1], u->b[2], u->b[3]);
    sink_u(u->b[3]);
    free(u);
}

int main(void)
    _preserves(_live(stdout))
    _preserves_value(stdout)
{
    /* Unbuffered: if a UB case crashes, we still see how far we got. */
    setvbuf(stdout, NULL, _IONBF, 0);
    case_12_1_store_whole_union_then_pun();
    return 0;
}
