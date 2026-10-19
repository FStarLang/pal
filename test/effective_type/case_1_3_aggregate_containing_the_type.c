/*
 * Standalone case 1.3: C11 effective type (6.5p6) and strict aliasing (6.5p7).
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
 *   cc -std=c11 -O2 -Wall -Wextra case_1_3_aggregate_containing_the_type.c -o case_1_3
 *   ./case_1_3
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
#include <stddef.h>

/* ------------------------------------------------------------------ */
/* Plumbing: opaque sinks so the optimizer cannot delete the accesses. */
/* ------------------------------------------------------------------ */

static volatile unsigned long long g_sink;

static void sink_u(unsigned long long v) { g_sink ^= v; }

#define BANNER(tag, title) \
    printf("\n== [%s] %s ==\n", tag, title)

/* A couple of plain aggregate types used throughout. */
struct point  { int x; int y; };

struct nested { double d; struct point pt; };

/* ================================================================== */
/* SECTION 1                                                          */
/* [DEFINED] Effective type IS defined (declared) and CANNOT change --  */
/*           and every access uses a permitted lvalue type.  (R1 + p7)  */
/* ================================================================== */

static void case_1_3_aggregate_containing_the_type(void)
{
    BANNER("DEFINED", "1.3: aggregate/union lvalue containing a member of the effective type");

    struct nested obj = { 2.5, { 7, 9 } };

    /* Accessing a member: the member subobject's declared type is int, and
       the lvalue `obj.pt.x` has type int.  Fine. */
    sink_u((unsigned)obj.pt.x);

    /* 6.5p7 bullet 4 runs the other way too: the whole struct may be read
       through a struct lvalue even though the members have their own
       effective types. */
    struct nested copy = obj;       /* struct assignment: legal. */
    printf("   copy.pt.y = %d, copy.d = %g\n", copy.pt.y, copy.d);

    /* A pointer to the first member of a struct and a pointer to the struct
       itself (6.7.2.1p15: no padding at the start) -- reading `.x` through
       `int *` is fine because the subobject's effective type IS int. */
    struct point pt = { 11, 13 };
    int *first = (int *)&pt;        /* ==&pt.x */
    sink_u((unsigned)*first);
    printf("   pt.x via struct pointer = %d\n", *first);
}

int main(void)
{
    /* Unbuffered: if a UB case crashes, we still see how far we got. */
    setvbuf(stdout, NULL, _IONBF, 0);
    case_1_3_aggregate_containing_the_type();
    return 0;
}
