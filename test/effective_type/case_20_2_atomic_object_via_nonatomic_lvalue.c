/*
 * Standalone case 20.2: C11 effective type (6.5p6) and strict aliasing (6.5p7).
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
 *   cc -std=c11 -O2 -Wall -Wextra case_20_2_atomic_object_via_nonatomic_lvalue.c -o case_20_2
 *   ./case_20_2
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
#include <stdint.h>
#include <stddef.h>

/* ------------------------------------------------------------------ */
/* Plumbing: opaque sinks so the optimizer cannot delete the accesses. */
/* ------------------------------------------------------------------ */

static volatile unsigned long long g_sink;

static void sink_u(unsigned long long v) { g_sink ^= v; }

static void sink_p(const void *v)        { g_sink ^= (unsigned long long)(uintptr_t)v; }

/* An "opaque" identity for pointers: defeats constant propagation without
   itself being UB. */
static void *opaque(void *p) { sink_p(p); return p; }

#define BANNER(tag, title) \
    printf("\n== [%s] %s ==\n", tag, title)

/* ================================================================== */
/* SECTION 20                                                         */
/* [UB] Qualification/atomicity mismatches that 6.5p7 does NOT forgive. */
/*      6.5p7 permits "a qualified version OF the effective type" --    */
/*      that direction only.  Dropping a qualifier is a different rule. */
/* ================================================================== */

#ifndef __STDC_NO_ATOMICS__
#include <stdatomic.h>
static _Atomic int g_atomic = 1;

static void case_20_2_atomic_object_via_nonatomic_lvalue(void)
{
    BANNER("UB", "20.2: object declared `_Atomic int`, accessed through a plain `int` lvalue");

    /* 6.2.5p27: an atomic type's size, representation and alignment need not
       match the corresponding unqualified type -- there may be a lock word
       in there.  `int` is neither compatible with nor a qualified version of
       `_Atomic int`, so this is a flat 6.5p7 violation (and on a lock-based
       implementation it also defeats the synchronisation entirely). */
    int *p = (int *)(uintptr_t)opaque((void *)(uintptr_t)&g_atomic);
    *p = 2;
    printf("   g_atomic = %d   <-- UB\n", (int)atomic_load(&g_atomic));
    sink_u((unsigned)*p);
}
#else
static void case_20_2_atomic_object_via_nonatomic_lvalue(void)
{
    BANNER("UB", "20.2: skipped -- no atomics on this implementation");
}
#endif

int main(void)
{
    /* Unbuffered: if a UB case crashes, we still see how far we got. */
    setvbuf(stdout, NULL, _IONBF, 0);
    case_20_2_atomic_object_via_nonatomic_lvalue();
    return 0;
}
