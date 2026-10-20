/*
 * Standalone case 7.4: C11 effective type (6.5p6) and strict aliasing (6.5p7).
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
 *   cc -std=c11 -O2 -Wall -Wextra case_7_4_vla_has_a_declared_type.c -o case_7_4
 *   ./case_7_4
 *
 * This executable runs its case unconditionally, including any UB.
 * Compile with -O2 (not -fno-strict-aliasing) to allow aliasing optimizations.
 * "It printed the right number" proves nothing about undefined behavior.
 * GCC/Clang warnings on UB cases are expected (-Warray-bounds,
 * -Wmaybe-uninitialized, -Wstrict-aliasing); running UB cases may crash.
 * Additional diagnostic builds can use -Wstrict-aliasing=2 -fstrict-aliasing
 * or -O1 -g -fsanitize=undefined,address; sanitizers do not detect all UB.
 */

#include "annotations.h"
#include <stdio.h>
#include <stddef.h>

/* ------------------------------------------------------------------ */
/* Plumbing: opaque sinks so the optimizer cannot delete the accesses. */
/* ------------------------------------------------------------------ */

static volatile unsigned long long g_sink;

static void sink_u(unsigned long long v) { g_sink ^= v; }

#define BANNER(tag, title) \
    printf("\n== [%s] %s ==\n", tag, title)

/* ================================================================== */
/* SECTION 7                                                          */
/* [DEFINED] LIFETIME boundaries -- an effective type is a property of  */
/*           an OBJECT, and objects begin and end.                      */
/* ================================================================== */

static void case_7_4_vla_has_a_declared_type(void)
    _requires(sizeof(int) <= SIZE_MAX / 4)
{
    BANNER("DEFINED", "7.4: a VLA has a declared type too (only its bound is dynamic)");

    size_t n = 4;
    int vla[n];                                /* declared type: int[n] */
    for (size_t i = 0; i < n; i++)
        _invariant(_live(i) && _live(n) && n == 4 && i <= n)
        _invariant((_slprop)_inline_pulse(
            exists* (v: Seq.seq (option Int32.t)).
            array_pts_to int32_t_ctype (maybe_repr int32_t_repr 4) 4
                (SizeT.v int32_t_alignof) $&(vla) 1.0R v **
            pure (Seq.length v == SizeT.v $(n)) **
            pure (forall (j: nat).
                j < Seq.length v /\ j < SizeT.v $(i) /\ j < 4 ==>
                Seq.index v j == Some (Int32.int_to_t (j * j)))))
        vla[i] = (int)(i * i);
    _assert(vla[0] == 0 && vla[1] == 1 && vla[2] == 4 && vla[3] == 9);
    printf("   vla = %d %d %d %d\n", vla[0], vla[1], vla[2], vla[3]);
    sink_u((unsigned)vla[3]);

    /* "Dynamically sized" is not the same as "dynamically typed": R1 pins
       this to int[], so reusing it as scratch space for a double is UB. */
}

int main(void)
    _preserves(_live(stdout))
    _preserves_value(stdout)
{
    /* Unbuffered: if a UB case crashes, we still see how far we got. */
    setvbuf(stdout, NULL, _IONBF, 0);
    case_7_4_vla_has_a_declared_type();
    return 0;
}
