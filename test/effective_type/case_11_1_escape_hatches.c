/*
 * Standalone case 11.1: C11 effective type (6.5p6) and strict aliasing (6.5p7).
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
 *   cc -std=c11 -O2 -Wall -Wextra case_11_1_escape_hatches.c -o case_11_1
 *   ./case_11_1
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
 * Case 2.2: Copying bytes into a declared object does not change its declared type.
 * Case 2.3: A declared union permits member punning; the resulting value can be unspecified or a trap representation.
 * Case 4.1: Successive non-character stores to allocated storage install new types; each read uses the most recently installed type.
 */

#include "annotations.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
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

#define BANNER(tag, title) \
    printf("\n== [%s] %s ==\n", tag, title)

union punner {
    int      i;
    float    f;
    unsigned char bytes[sizeof(float) > sizeof(int) ? sizeof(float) : sizeof(int)];
};

#if defined(__GNUC__)
typedef int __attribute__((__may_alias__)) aliasing_int;
#endif

/* ================================================================== */
/* SECTION 11                                                         */
/* The sanctioned escape hatches, and the unsanctioned-but-popular one. */
/* ================================================================== */

static void case_11_1_escape_hatches(void)
{
    BANNER("DEFINED", "11.1: how to pun WITHOUT invoking 6.5p7");

    float f = 2.5f;
    uint32_t bits;

    /* 1. memcpy into an object of the target declared type (2.2).  This is the
          portable, standard, zero-cost-after-optimization answer. */
    memcpy(&bits, &f, sizeof bits);
    printf("   (1) memcpy      : %#" PRIx32 "\n", bits);

    /* 2. A union (2.3): the access is legal; only the VALUE is unspecified. */
    union punner u; u.f = f;
    printf("   (2) union       : %#x\n", (unsigned)u.i);

    /* 3. Character-type lvalues (2.1): always legal, any object. */
    _array unsigned char *b = (unsigned char *)&f;
    printf("   (3) char access : %02x%02x%02x%02x\n", b[3], b[2], b[1], b[0]);

    /* 4. Re-typing genuinely untyped (allocated) storage (4.1). */
    void *p = malloc(sizeof(float));
    if (p) { *(float *)p = f; *(uint32_t *)p = 0; free(p); }
    printf("   (4) re-type allocated storage: ok\n");

    /* 5. NON-STANDARD: compiler extensions.  These are promises by the
          implementation, not by the standard.
            - GCC/Clang: __attribute__((__may_alias__))
            - GCC/Clang/ICC: -fno-strict-aliasing (disables the optimization,
              does NOT make the program conforming)
            - MSVC: no strict-aliasing optimizations at all today
          They make real code work; they do not make it portable. */
#if defined(__GNUC__)
    aliasing_int *ai = (aliasing_int *)opaque(&f);
    printf("   (5) may_alias   : %#x  (GCC/Clang extension, NOT standard C)\n",
           (unsigned)*ai);
    sink_u((unsigned)*ai);
#else
    puts("   (5) may_alias   : n/a on this compiler");
#endif
    sink_u(bits);
}

int main(void)
    _preserves(_live(stdout))
    _preserves_value(stdout)
{
    /* Unbuffered: if a UB case crashes, we still see how far we got. */
    setvbuf(stdout, NULL, _IONBF, 0);
    case_11_1_escape_hatches();
    return 0;
}
