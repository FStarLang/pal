/*
 * Standalone case 10.1: C11 effective type (6.5p6) and strict aliasing (6.5p7).
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
 *   cc -std=c11 -O2 -Wall -Wextra case_10_1_flexible_array_member.c -o case_10_1
 *   ./case_10_1
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
#include <stdlib.h>
#include <stddef.h>

/* ------------------------------------------------------------------ */
/* Plumbing: opaque sinks so the optimizer cannot delete the accesses. */
/* ------------------------------------------------------------------ */

static volatile unsigned long long g_sink;

static void sink_u(unsigned long long v) { g_sink ^= v; }

#define BANNER(tag, title) \
    printf("\n== [%s] %s ==\n", tag, title)

struct fam { size_t n; int a[]; };

/* ================================================================== */
/* SECTION 10                                                         */
/* Flexible array members, padding bytes, and memset.                   */
/* ================================================================== */

static void case_10_1_flexible_array_member(void)
{
    BANNER("DEFINED", "10.1: a flexible array member in allocated storage");

    size_t n = 4;
    struct fam *f = malloc(sizeof *f + n * sizeof(int));
    if (!f) return;

    /* The allocated object has no declared type, so each store installs the
       effective type of the bytes it writes (R2): `size_t` for .n and `int`
       for each element.  6.7.2.1p18 blesses the `f->a[i]` lvalues as long as
       the allocation is big enough. */
    f->n = n;
    for (size_t i = 0; i < n; i++)
        _invariant(_live(i) && _live(n) && n == 4 && i <= n)
        _invariant((_slprop)_inline_pulse(
            exists* (v: Seq.seq (option Int32.t)).
            array_pts_to (maybe_repr int32_t_repr 4) 4
                (SizeT.v int32_t_alignof) ($(f) +! struct_fam_offsetof_a) 1.0R v **
            pure (Seq.length v == SizeT.v $(n)) **
            pure (forall (j: nat).
                j < Seq.length v /\ j < SizeT.v $(i) /\ j < 4 ==>
                Seq.index v j == Some (Int32.int_to_t (j * 10)))))
        f->a[i] = (int)(i * 10);
    printf("   fam n=%zu a=[%d %d %d %d]\n", f->n, f->a[0], f->a[1], f->a[2], f->a[3]);
    sink_u((unsigned)f->a[3]);
    free(f);
}

int main(void)
    _preserves(_live(stdout))
    _preserves_value(stdout)
{
    /* Unbuffered: if a UB case crashes, we still see how far we got. */
    setvbuf(stdout, NULL, _IONBF, 0);
    case_10_1_flexible_array_member();
    return 0;
}
