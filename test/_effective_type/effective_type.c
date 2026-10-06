/*
 * effective_type.c -- An exhaustive tour of C11 6.5p6 ("effective type")
 * and its consumer, C11 6.5p7 (the "strict aliasing" rule).
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
 * ---------------------------------------------------------------------------
 * HOW TO BUILD / RUN
 *
 *   cc -std=c11 -O2 -Wall -Wextra -o effective_type effective_type.c
 *   ./effective_type          # runs ONLY the well-defined cases
 *   ./effective_type ub       # ALSO runs the undefined-behavior cases
 *
 * The UB cases are compiled but never *called* unless you pass "ub", so the
 * default run stays strictly conforming.  Compile with -O2 (not
 * -fno-strict-aliasing) if you want a chance of observing real misbehavior;
 * note that "it printed the right number" proves nothing about UB.
 *
 * Expect warnings from GCC/Clang on the UB cases (-Warray-bounds,
 * -Wmaybe-uninitialized, -Wstrict-aliasing): that is the point.  The "ub" run
 * ends with SIGSEGV in case 22.2, which writes to a string literal -- that is
 * the last case for exactly that reason.  Try also:
 *     cc -std=c11 -O1 -g -fsanitize=undefined,address  (catches 12.5/16.1/16.2/22.2)
 *     cc -std=c11 -O2 -Wstrict-aliasing=2 -fstrict-aliasing
 *
 * Things actually observed on x86-64 GCC 13 at -O2:
 *   - 15.1 prints bad2=5 even though `*pd = 1.5` was stored first: the compiler
 *     assumed `int *` and `double *` cannot alias and reordered.
 *   - 15.4 prints 9.75 after `*(int *)p = 1` clobbered the low half.
 *   - 20.1 returns 1 although memory holds 2: `restrict` let the compiler keep
 *     the stale value, with no type mismatch anywhere in sight.
 *   - 21.2 prints 2 rather than 7: the dead stack slot was recycled.
 *   - 10.2's memcmp reports DIFFERENT for two structs with identical members.
 *
 * ---------------------------------------------------------------------------
 * SECTION INDEX
 *    1  defined   declared type, unchangeable, accessed correctly
 *    2  defined   unchangeable type, but character access is always legal
 *    3  defined   allocated storage acquires an effective type (R2)
 *    4  defined   allocated storage re-typed repeatedly
 *    5  defined   R3 propagation via memcpy / character-array copy
 *    6  defined   R4 fallback; character stores do NOT install a type
 *    7  defined   lifetimes: free/malloc, block reuse, compound literals, VLAs
 *    8  defined   union common initial sequence; first-member "inheritance"
 *    9  impl-def  enum vs its compatible integer type; the 3 character types
 *   10  defined   flexible array members, padding bytes, memset
 *   11  defined   the sanctioned ways to type-pun (plus may_alias, which isn't)
 *   12  UB        fixed type, forbidden lvalue type
 *   13  UB        trying to change a type that R1 has pinned
 *   14  UB        installed type, then an incompatible access
 *   15  UB        re-typed at the WRONG TIME
 *   16  UB        re-typed to a PROBLEMATIC type
 *   17  UB        R3 subtleties: untyped sources, partial copies
 *   18  UB        R4 allows the type, but the value is indeterminate
 *   19  UB        qualifier / atomicity mismatches (volatile, _Atomic)
 *   20  UB        types match perfectly, `restrict` promise broken
 *   21  UB        the object is gone (freed, out of scope, temporary lifetime)
 *   22  UB        declared objects that may not be modified at all
 *
 * Every case below is tagged:
 *     [DEFINED]  strictly conforming
 *     [UB]       undefined behavior, per the cited rule
 *     [UNSPEC]   defined as far as 6.5p6/p7 go, but another rule bites
 * ---------------------------------------------------------------------------
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>
#include <limits.h>
#include <inttypes.h>

/* ------------------------------------------------------------------ */
/* Plumbing: opaque sinks so the optimizer cannot delete the accesses. */
/* ------------------------------------------------------------------ */

static volatile unsigned long long g_sink;

static void sink_u(unsigned long long v) { g_sink ^= v; }
static void sink_d(double v)             { g_sink ^= (unsigned long long)(v * 7.0); }
static void sink_p(const void *v)        { g_sink ^= (unsigned long long)(uintptr_t)v; }

/* An "opaque" identity for pointers: defeats constant propagation without
   itself being UB. */
static void *opaque(void *p) { sink_p(p); return p; }

#define BANNER(tag, title) \
    printf("\n== [%s] %s ==\n", tag, title)

/* A couple of plain aggregate types used throughout. */
struct point  { int x; int y; };
struct nested { double d; struct point pt; };

union punner {
    int      i;
    float    f;
    unsigned char bytes[sizeof(float) > sizeof(int) ? sizeof(float) : sizeof(int)];
};

/* ================================================================== */
/* SECTION 1                                                          */
/* [DEFINED] Effective type IS defined (declared) and CANNOT change --  */
/*           and every access uses a permitted lvalue type.  (R1 + p7)  */
/* ================================================================== */

static void case_1_1_declared_type_accessed_as_itself(void)
{
    BANNER("DEFINED", "1.1: declared type, accessed through its own type");

    int n = 42;                 /* declared type: int. Effective type: int.
                                   Forever. Nothing can change that. */
    int *p = &n;
    *p = 43;                    /* lvalue type int == effective type int. OK. */
    printf("   n = %d\n", *p);
    sink_u((unsigned)n);
}

static void case_1_2_qualified_and_signedness_variants(void)
{
    BANNER("DEFINED", "1.2: qualified version + signed/unsigned counterpart");

    int n = 0x01020304;

    /* 6.5p7 bullet 2: a *qualified version* of the effective type. */
    const volatile int *cvp = &n;
    sink_u((unsigned)*cvp);

    /* 6.5p7 bullet 3: the signed-or-unsigned type corresponding to the
       effective type.  Reading an `int` object through `unsigned int *`
       is explicitly permitted (the value may be converted, but the ACCESS
       is legal). */
    unsigned int *up = (unsigned int *)&n;
    printf("   as unsigned: %#x\n", *up);
    sink_u(*up);

    /* ...and the combination: `const unsigned int *`. */
    const unsigned int *cup = (const unsigned int *)&n;
    sink_u(*cup);
}

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

/* ================================================================== */
/* SECTION 2                                                          */
/* [DEFINED] Effective type is fixed, but CHARACTER-type access is      */
/*           always permitted (6.5p7 last bullet).                      */
/* ================================================================== */

static void case_2_1_inspect_any_object_as_bytes(void)
{
    BANNER("DEFINED", "2.1: character-type lvalues may access ANY effective type");

    double d = 1.0;
    /* Effective type of `d` is double and is unchangeable.  But a character
       lvalue is always allowed, so dumping the representation is legal. */
    unsigned char *b = (unsigned char *)&d;
    printf("   repr of 1.0:");
    for (size_t i = 0; i < sizeof d; i++)
        printf(" %02x", b[i]);
    putchar('\n');
    sink_u(b[0]);
}

static void case_2_2_memcpy_out_of_a_declared_object(void)
{
    BANNER("DEFINED", "2.2: memcpy is defined as a character-wise copy");

    float   f = 3.5f;
    uint32_t bits;

    /* The canonical, *legal* way to type-pun: copy the bytes into an object
       whose declared type is the one you want.  `bits` has declared type
       uint32_t (R1), so reading it as uint32_t is correct; memcpy touched it
       only through character types. */
    memcpy(&bits, &f, sizeof bits < sizeof f ? sizeof bits : sizeof f);
    printf("   float 3.5f reinterpreted as uint32_t = %#" PRIx32 "\n", bits);
    sink_u(bits);
}

static void case_2_3_union_punning(void)
{
    BANNER("DEFINED", "2.3: union member punning (6.5.2.3, footnote 95)");

    /* A union has a DECLARED type (R1): the union type.  6.5p7 bullet 4 lets
       you access it through a union lvalue, and 6.5.2.3p3 footnote 95 (plus
       C11 Annex J.1 "unspecified") blesses reading a member other than the
       one last stored -- the *bytes* are reinterpreted, which is unspecified
       (possibly a trap representation), but it is NOT an aliasing violation. */
    union punner u;
    u.f = 1.5f;
    printf("   u.f=1.5f read back as u.i = %d (value unspecified, access legal)\n", u.i);
    sink_u((unsigned)u.i);
}

/* ================================================================== */
/* SECTION 3                                                          */
/* [DEFINED] No declared type; a store THROUGH A NON-CHARACTER LVALUE   */
/*           installs the effective type (R2), reads then agree.        */
/* ================================================================== */

static void case_3_1_malloc_store_then_read(void)
{
    BANNER("DEFINED", "3.1: allocated object acquires an effective type from a store (R2)");

    void *p = malloc(sizeof(double));
    if (!p) return;

    /* Before this line the object has NO effective type at all. */
    *(double *)p = 2.25;        /* R2: effective type of those sizeof(double)
                                   bytes is now `double`. */
    double d = *(double *)p;    /* non-modifying access with the matching
                                   type: permitted by R2 + 6.5p7. */
    printf("   *(double*)p = %g\n", d);
    sink_d(d);
    free(p);
}

static void case_3_2_effective_type_survives_nonmodifying_accesses(void)
{
    BANNER("DEFINED", "3.2: the effective type persists across many reads");

    int *p = malloc(sizeof(int));
    if (!p) return;

    *p = 1000;                  /* effective type := int */
    for (int i = 0; i < 3; i++) /* each of these is a *non-modifying* access, */
        sink_u((unsigned)*p);   /* so the effective type stays `int`. */

    /* A *modifying* access through the SAME type is of course also fine and
       simply re-installs the same effective type. */
    *p += 1;
    printf("   *p = %d\n", *p);
    free(p);
}

static void case_3_3_struct_effective_type_then_member_access(void)
{
    BANNER("DEFINED", "3.3: effective type set to a struct, members read individually");

    void *raw = malloc(sizeof(struct point));
    if (!raw) return;

    struct point *sp = raw;
    *sp = (struct point){ 5, 6 };   /* R2: effective type := struct point
                                       (and, for the subobjects, their
                                       respective member types). */
    /* The member subobjects now have effective type int, so an `int *` is a
       permitted lvalue for them. */
    int *px = (int *)&sp->x;
    printf("   sp->x via int* = %d, sp->y = %d\n", *px, sp->y);
    sink_u((unsigned)*px);
    free(raw);
}

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
       re-typing store.  That is what makes 4.1 defined and 15.1 (below) not. */
    free(p);
}

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

/* ================================================================== */
/* SECTION 5                                                          */
/* [DEFINED] R3: memcpy/memmove and character-array copies PROPAGATE    */
/*           the source object's effective type.                        */
/* ================================================================== */

static void case_5_1_memcpy_propagates_effective_type(void)
{
    BANNER("DEFINED", "5.1: memcpy into allocated storage copies the source's effective type (R3)");

    double src = 6.75;                  /* declared type double */
    void  *dst = malloc(sizeof(double));
    if (!dst) return;

    memcpy(dst, &src, sizeof src);      /* R3: effective type of *dst becomes
                                           `double` -- NOT `unsigned char[]`,
                                           even though memcpy copies bytes. */
    printf("   *(double*)dst = %g\n", *(double *)dst);   /* legal */
    sink_d(*(double *)dst);
    free(dst);
}

static void case_5_2_character_array_copy_propagates(void)
{
    BANNER("DEFINED", "5.2: a hand-rolled character-wise copy also propagates (R3)");

    struct point src = { 21, 22 };      /* declared type struct point */
    void *dst = malloc(sizeof src);
    if (!dst) return;

    /* "or is copied as an array of character type" -- an explicit byte loop
       counts, exactly like memcpy. */
    const unsigned char *s = (const unsigned char *)&src;
    unsigned char       *d = dst;
    for (size_t i = 0; i < sizeof src; i++)
        d[i] = s[i];

    struct point *dp = dst;             /* effective type is struct point */
    printf("   copied struct = {%d,%d}\n", dp->x, dp->y);
    sink_u((unsigned)dp->x);
    free(dst);
}

static void case_5_3_memcpy_allocated_to_allocated(void)
{
    BANNER("DEFINED", "5.3: R3 chains -- effective type flows allocated -> allocated");

    void *a = malloc(sizeof(float));
    void *b = malloc(sizeof(float));
    if (!a || !b) { free(a); free(b); return; }

    *(float *)a = 0.5f;                 /* R2: a's effective type := float */
    memcpy(b, a, sizeof(float));        /* R3: b's effective type := float
                                           (the source "has one") */
    printf("   *(float*)b = %g\n", (double)*(float *)b);
    sink_d(*(float *)b);
    free(a); free(b);
}

/* ================================================================== */
/* SECTION 6                                                          */
/* [DEFINED-ish] R4: no declared type and no effective type installed   */
/*           -> the effective type is simply the lvalue's type.         */
/* ================================================================== */

static void case_6_1_fresh_malloc_write_is_always_legal(void)
{
    BANNER("DEFINED", "6.1: untouched allocated bytes have NO effective type (R4)");

    /* Nothing has been stored yet, so there is no prior effective type for a
       later lvalue to conflict with.  Whatever type you first use *is* the
       effective type (R2 for a store, R4 for anything else). */
    void *p = malloc(sizeof(long double));
    if (!p) return;

    *(long double *)p = 1.5L;           /* first touch wins */
    printf("   *(long double*)p = %Lg\n", *(long double *)p);
    sink_d((double)*(long double *)p);
    free(p);
}

static void case_6_2_character_store_does_NOT_install_a_type(void)
{
    BANNER("DEFINED", "6.2: storing through a CHARACTER lvalue leaves the object untyped (R2 caveat)");

    void *p = calloc(1, sizeof(int));
    if (!p) return;

    /* R2 only fires for a "lvalue having a type that is NOT a character
       type".  So these stores do NOT make the effective type
       `unsigned char`: the object still has no effective type. */
    unsigned char *b = p;
    for (size_t i = 0; i < sizeof(int); i++)
        b[i] = (unsigned char)(i + 1);

    /* Therefore R4 applies to the following read, and the effective type for
       THIS access is simply `int`.  No aliasing violation.  (The *value* is
       whatever those bytes mean, and could in principle be a trap
       representation for some types -- but not for unsigned types.) */
    unsigned int v = *(unsigned int *)p;
    printf("   bytes 01 02 03 04... read as unsigned = %#x\n", v);
    sink_u(v);
    free(p);
}

static void case_6_3_calloc_then_read_as_unsigned(void)
{
    BANNER("DEFINED", "6.3: calloc gives all-zero bytes; reading as an unsigned type is safe");

    void *p = calloc(1, sizeof(unsigned long));
    if (!p) return;
    /* calloc's zeroing is specified byte-wise, so (like 6.2) no effective type
       is installed; R4 lets this read use `unsigned long`.  All-zero bytes
       are never a trap representation for an unsigned integer type, so the
       value is determinate: 0. */
    printf("   calloc'd unsigned long = %lu\n", *(unsigned long *)p);
    sink_u(*(unsigned long *)p);
    free(p);
}

/* ================================================================== */
/* SECTION 7                                                          */
/* [DEFINED] LIFETIME boundaries -- an effective type is a property of  */
/*           an OBJECT, and objects begin and end.                      */
/* ================================================================== */

static void case_7_1_free_then_malloc_resets_everything(void)
{
    BANNER("DEFINED", "7.1: free() ends the object; a new malloc starts a fresh, untyped one");

    void *p = malloc(sizeof(double));
    if (!p) return;
    *(double *)p = 1.5;          /* effective type := double */
    free(p);                     /* object's lifetime ends                */

    /* Even if the allocator hands back the very same address, this is a
       DIFFERENT object with no effective type.  R2/R4 start over. */
    void *q = malloc(sizeof(double));
    if (!q) return;
    *(long *)q = 99;             /* perfectly fine: new object, new type  */
    printf("   recycled storage as long = %ld\n", *(long *)q);
    sink_u((unsigned long long)*(long *)q);
    free(q);
}

static void case_7_2_automatic_storage_reuse_across_blocks(void)
{
    BANNER("DEFINED", "7.2: two declared objects may occupy the same bytes at different times");

    /* The two blocks have disjoint lifetimes, so the implementation may give
       `a` and `d` the same stack slot.  R1 pins each object's effective type
       *for its own lifetime only*; there is no conflict and no re-typing. */
    { int    a = 1;   sink_u((unsigned)a);   printf("   block 1: int    %d\n", a); }
    { double d = 2.5; sink_d(d);             printf("   block 2: double %g\n", d); }
}

static void case_7_3_compound_literals_have_a_declared_type(void)
{
    BANNER("DEFINED", "7.3: a compound literal is an unnamed object WITH a declared type");

    /* 6.5.2.5p5: the compound literal's type name gives it a declared type,
       so R1 applies -- it behaves like a named variable, not like malloc.
       At block scope it has automatic storage duration. */
    int *p = (int[]){ 10, 20, 30 };          /* declared type int[3] */
    printf("   compound literal: %d %d %d\n", p[0], p[1], p[2]);
    sink_u((unsigned)p[1]);

    struct point *sp = &(struct point){ 4, 5 };   /* declared type struct point */
    printf("   compound struct : {%d,%d}\n", sp->x, sp->y);
    sink_u((unsigned)sp->y);

    /* Consequently `*(float *)p` would be UB exactly as in section 12 -- a
       compound literal can NOT be re-typed. */
}

static void case_7_4_vla_has_a_declared_type(void)
{
    BANNER("DEFINED", "7.4: a VLA has a declared type too (only its bound is dynamic)");

    size_t n = 4;
    int vla[n];                                /* declared type: int[n] */
    for (size_t i = 0; i < n; i++) vla[i] = (int)(i * i);
    printf("   vla = %d %d %d %d\n", vla[0], vla[1], vla[2], vla[3]);
    sink_u((unsigned)vla[3]);

    /* "Dynamically sized" is not the same as "dynamically typed": R1 pins
       this to int[], so reusing it as scratch space for a double is UB. */
}

/* ================================================================== */
/* SECTION 8                                                          */
/* [DEFINED] Two structural escape hatches people often forget:         */
/*           the common initial sequence rule and first-member casts.   */
/* ================================================================== */

struct cis_a { int tag; int x; };
struct cis_b { int tag; double y; };
union  cis   { struct cis_a a; struct cis_b b; };   /* declaration visible */

static void case_8_1_common_initial_sequence(void)
{
    BANNER("DEFINED", "8.1: union common initial sequence (6.5.2.3p6) -- the exception to 12.3");

    union cis u;
    u.b.tag = 7;
    u.b.y   = 1.5;

    /* 6.5.2.3p6: because a declaration of the complete union type is visible
       and the two members share a common initial sequence (`int tag`), it is
       permitted to inspect the common part through EITHER member. */
    printf("   wrote via .b, read via .a: tag = %d\n", u.a.tag);
    sink_u((unsigned)u.a.tag);

    /* Contrast with 12.3: without the union, two layout-identical struct types
       are simply incompatible and punning between them is UB. */
}

struct base    { int kind; const char *name; };
struct derived { struct base base; int extra; };

static void case_8_2_first_member_upcast(void)
{
    BANNER("DEFINED", "8.2: struct 'inheritance' via a first-member cast (6.7.2.1p15)");

    struct derived d = { { 1, "derived" }, 42 };

    /* 6.7.2.1p15: "A pointer to a structure object, suitably converted,
       points to its initial member."  The subobject `d.base` genuinely has
       effective type `struct base`, so this is not punning at all. */
    struct base *bp = (struct base *)&d;
    printf("   bp->kind = %d, bp->name = %s\n", bp->kind, bp->name);
    sink_u((unsigned)bp->kind);

    /* Downcast back is equally fine, because the pointer really does point
       into an object whose effective type is `struct derived`. */
    struct derived *dp = (struct derived *)bp;
    printf("   dp->extra = %d\n", dp->extra);
    sink_u((unsigned)dp->extra);
}

/* ================================================================== */
/* SECTION 9                                                          */
/* [IMPL-DEFINED] Types that may or may not be compatible depending on  */
/*                the implementation, and the three character types.    */
/* ================================================================== */

enum color { RED, GREEN, BLUE };

static void case_9_1_enum_vs_its_compatible_integer_type(void)
{
    BANNER("IMPL-DEF", "9.1: `enum E` is compatible with an IMPLEMENTATION-CHOSEN integer type");

    enum color c = GREEN;

    /* 6.7.2.2p4: "Each enumerated type shall be compatible with char, a
       signed integer type, or an unsigned integer type.  The choice of type
       is implementation-defined."  GCC/Clang on this ABI pick `unsigned int`
       for an all-non-negative enumeration, so `unsigned int *` happens to be
       a compatible lvalue -- and `int *` is then allowed as its signed
       counterpart.  Portable code cannot rely on either. */
    unsigned int *up = (unsigned int *)&c;
    printf("   sizeof(enum color)=%zu, as unsigned = %u   <-- implementation-defined\n",
           sizeof c, *up);
    sink_u(*up);
}

static void case_9_2_the_three_character_types(void)
{
    BANNER("DEFINED", "9.2: char / signed char / unsigned char are 3 DISTINCT but interchangeable-for-access types");

    char c = 'A';

    /* 6.2.5p15: `char` is a separate type from both `signed char` and
       `unsigned char`, and none of the three is compatible with another.
       Normally that would make the next two lines UB -- but 6.5p7's final
       bullet ("a character type") covers all three unconditionally. */
    signed char   *sp = (signed char *)&c;
    unsigned char *up = (unsigned char *)&c;
    printf("   as char=%c signed char=%d unsigned char=%u\n", c, *sp, *up);
    sink_u(*up);

    /* Note the asymmetry: a character lvalue may access ANY object, but a
       non-character lvalue may never access a `char` object (see 12.4). */
}

/* ================================================================== */
/* SECTION 10                                                         */
/* Flexible array members, padding bytes, and memset.                   */
/* ================================================================== */

struct fam { size_t n; int a[]; };

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
    for (size_t i = 0; i < n; i++) f->a[i] = (int)(i * 10);
    printf("   fam n=%zu a=[%d %d %d %d]\n", f->n, f->a[0], f->a[1], f->a[2], f->a[3]);
    sink_u((unsigned)f->a[3]);
    free(f);
}

static void case_10_2_padding_bytes(void)
{
    BANNER("UNSPEC", "10.2: padding bytes have unspecified values -- memcmp on structs is a trap");

    struct padded { char c; int i; };

    struct padded x, y;
    memset(&x, 0, sizeof x);
    memset(&y, 0xFF, sizeof y);
    /* 6.2.6.1p6: when a value is stored into a structure, the bytes that
       correspond to padding take UNSPECIFIED values -- the earlier memset is
       not guaranteed to survive these member stores. */
    x.c = 'a'; x.i = 1;
    y.c = 'a'; y.i = 1;

    printf("   members equal; memcmp says %s   <-- unspecified, not a bug in your code\n",
           memcmp(&x, &y, sizeof x) == 0 ? "equal" : "DIFFERENT");
    sink_u((unsigned)x.i);
}

static void case_10_3_memset_does_not_install_a_type(void)
{
    BANNER("DEFINED", "10.3: memset writes through character types, so R2 does not fire");

    void *p = malloc(sizeof(unsigned long));
    if (!p) return;

    memset(p, 0, sizeof(unsigned long));   /* character-type stores: the
                                              object still has NO effective
                                              type (cf. 6.2/6.3). */
    /* R4 therefore lets any lvalue type be used; all-zero bytes are a valid
       representation of 0 for any unsigned integer type. */
    printf("   memset'd unsigned long = %lu\n", *(unsigned long *)p);
    sink_u(*(unsigned long *)p);
    free(p);
}

/* ================================================================== */
/* SECTION 11                                                         */
/* The sanctioned escape hatches, and the unsanctioned-but-popular one. */
/* ================================================================== */

#if defined(__GNUC__)
typedef int __attribute__((__may_alias__)) aliasing_int;
#endif

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
    unsigned char *b = (unsigned char *)&f;
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

/* ================================================================== */
/* SECTION 12                                                         */
/* [UB] Effective type IS defined (declared) and CANNOT change, and the */
/*      access uses a disallowed lvalue type.                           */
/* ================================================================== */

static void case_12_1_read_int_as_float(void)
{
    BANNER("UB", "12.1: object declared `int`, read through `float *`");

    int n = 0x3f800000;
    float *pf = (float *)opaque(&n);
    /* UB: effective type is `int` (R1, unchangeable).  `float` is not
       compatible with int, not a qualified/signed variant, not an aggregate
       containing an int, and not a character type.  6.5p7 violated. */
    printf("   *(float*)&n = %g   <-- UB\n", (double)*pf);
    sink_d(*pf);
}

static void case_12_2_write_int_through_short(void)
{
    BANNER("UB", "12.2: object declared `int`, written through `short *`");

    int n = 1;
    short *ps = (short *)opaque(&n);
    *ps = 2;                 /* UB: `short` is neither compatible with `int`
                                nor its signed/unsigned counterpart.  And note
                                this store does NOT change the effective type:
                                R2 applies only to objects with no declared
                                type. */
    printf("   n = %d   <-- UB\n", n);
    sink_u((unsigned)n);
}

static void case_12_3_struct_pun_between_layout_compatible_types(void)
{
    BANNER("UB", "12.3: two distinct struct types with identical layout are NOT compatible");

    struct a { int x, y; };
    struct b { int x, y; };          /* same layout, DIFFERENT type */

    struct a va = { 1, 2 };
    struct b *pb = (struct b *)opaque(&va);
    /* UB: compatibility of structs declared in the same translation unit
       requires the same tag (6.2.7p1).  Layout identity is irrelevant. */
    printf("   pb->x = %d   <-- UB\n", pb->x);
    sink_u((unsigned)pb->x);
}

static void case_12_4_char_array_used_as_int_storage(void)
{
    BANNER("UB", "12.4: `static char buf[]` reused as an int -- the classic bug");

    static char buf[sizeof(int) * 2];  /* DECLARED type: char[8].  R1 pins the
                                          effective type of every byte to
                                          `char` forever. */
    int *pi = (int *)opaque(buf);
    *pi = 0x11223344;                  /* UB: writing through `int *`.  Unlike
                                          malloc'd storage, this buffer HAS a
                                          declared type, so R2 cannot fire and
                                          the effective type cannot change. */
    printf("   buf as int = %d   <-- UB (also likely misaligned)\n", *pi);
    sink_u((unsigned)*pi);
}

static void case_12_5_alignment_of_declared_char_buffer(void)
{
    BANNER("UB", "12.5: same as 12.4 plus an alignment violation");

    static char buf[32];
    /* Even with _Alignas this would still be an effective-type violation;
       without it, the cast itself is UB (6.3.2.3p7) if buf is not suitably
       aligned for `double`. */
    double *pd = (double *)opaque(buf + 1);   /* deliberately odd offset */
    *pd = 1.0;                                 /* UB x2 */
    printf("   %g   <-- UB\n", *pd);
    sink_d(*pd);
}

/* ================================================================== */
/* SECTION 13                                                         */
/* [UB] Attempting to CHANGE an effective type that is fixed by R1.     */
/* ================================================================== */

static void case_13_1_memcpy_cannot_retype_a_declared_object(void)
{
    BANNER("UB", "13.1: memcpy into a DECLARED object does not re-type it (R3 needs 'no declared type')");

    double src = 1.0;
    int    dst = 0;        /* declared type int -- permanently */

    memcpy(opaque(&dst), &src, sizeof dst);  /* the memcpy itself is fine:
                                                character-wise access. */
    /* R3 explicitly applies only to "an object having no declared type".
       `dst` has one, so its effective type is still `int`... which means the
       next line is LEGAL (int lvalue, int effective type) but the VALUE is a
       reinterpretation of double bytes and may be a trap representation
       (6.2.6.1p5 -> UB on read). */
    printf("   dst = %d   <-- value unspecified / possibly a trap rep\n", dst);
    sink_u((unsigned)dst);

    /* THIS, however, is a plain 6.5p7 violation: */
    double *pd = (double *)opaque(&dst);
    printf("   *(double*)&dst = %g   <-- UB\n", *pd);
    sink_d(*pd);
}

static void case_13_2_store_does_not_retype_automatic_storage(void)
{
    BANNER("UB", "13.2: storing a float into an `int` variable does not install `float`");

    int n = 0;
    float *pf = (float *)opaque(&n);
    *pf = 1.0f;            /* UB immediately: the effective type of `n` is int
                              and R2 cannot fire for a declared object.  A
                              naive reading of R2 ("a store installs the
                              lvalue's type") is exactly the trap this case
                              exists to illustrate. */
    printf("   n = %d, *pf = %g   <-- UB\n", n, (double)*pf);
    sink_u((unsigned)n);
}

static void case_13_3_reuse_of_a_declared_struct_as_another_struct(void)
{
    BANNER("UB", "13.3: an arena carved out of a declared array cannot be re-typed");

    /* A very common "custom allocator" mistake: the backing store has a
       declared type, so every object carved out of it is permanently
       `unsigned char`. */
    static unsigned char arena[128];
    struct point *p = (struct point *)opaque(arena);
    *p = (struct point){ 3, 4 };   /* UB */
    printf("   arena as struct point = {%d,%d}   <-- UB\n", p->x, p->y);
    sink_u((unsigned)p->x);

    /* The conforming fix is to obtain the storage from malloc/calloc/realloc/
       aligned_alloc, which produce objects with NO declared type. */
}

/* ================================================================== */
/* SECTION 14                                                         */
/* [UB] No declared type, an effective type WAS installed, and a later  */
/*      access uses an incompatible lvalue type without re-typing.      */
/* ================================================================== */

static void case_14_1_installed_int_read_as_float(void)
{
    BANNER("UB", "14.1: allocated object typed `int` by a store, then read as `float`");

    void *p = malloc(sizeof(float) > sizeof(int) ? sizeof(float) : sizeof(int));
    if (!p) return;

    *(int *)p = 0x3f800000;     /* R2: effective type := int */
    float f = *(float *)opaque(p);   /* UB: this is a NON-modifying access, so
                                        R2's "and for subsequent accesses that
                                        do not modify the stored value" keeps
                                        the effective type at `int`.  Reading
                                        through `float *` violates 6.5p7. */
    printf("   = %g   <-- UB\n", (double)f);
    sink_d(f);
    free(p);
}

static void case_14_2_installed_struct_read_as_unrelated_struct(void)
{
    BANNER("UB", "14.2: allocated object typed `struct point`, read as `struct nested`");

    void *p = malloc(sizeof(struct nested));
    if (!p) return;

    *(struct point *)p = (struct point){ 1, 2 };    /* effective type := struct point */
    struct nested *np = (struct nested *)opaque(p);
    printf("   np->d = %g   <-- UB\n", np->d);      /* UB: incompatible types */
    sink_d(np->d);
    free(p);
}

static void case_14_3_memcpy_installed_type_then_wrong_read(void)
{
    BANNER("UB", "14.3: R3 installed `double`; reading as `long long` is still UB");

    double src = 1.0;
    void  *dst = malloc(sizeof(double));
    if (!dst) return;

    memcpy(dst, &src, sizeof src);        /* R3: effective type := double */
    long long *pll = (long long *)opaque(dst);
    printf("   bits = %lld   <-- UB\n", *pll);
    sink_u((unsigned long long)*pll);
    free(dst);
}

/* ================================================================== */
/* SECTION 15                                                         */
/* [UB] The effective type CAN change, but the change happens at the    */
/*      WRONG TIME relative to the accesses.                            */
/* ================================================================== */

static void case_15_1_read_before_the_retyping_store(void)
{
    BANNER("UB", "15.1: reading through the NEW type before the re-typing store happens");

    void *p = malloc(sizeof(double));
    if (!p) return;

    int    *pi = p;
    double *pd = p;

    *pi = 5;                 /* effective type := int                        */
    double bad = *pd;        /* UB: effective type is STILL int here.  A read
                                never re-types; only a store does (R2).      */
    *pd = 1.5;               /* NOW the effective type becomes double...     */
    int bad2 = *pi;          /* ...so this read is UB in the other direction. */

    printf("   bad=%g bad2=%d   <-- both UB\n", bad, bad2);
    sink_d(bad); sink_u((unsigned)bad2);
    free(p);
}

static void case_15_2_interleaved_accesses_across_a_call(void)
{
    BANNER("UB", "15.2: a live pointer of the OLD type used after a re-typing store");

    void *p = malloc(sizeof(double));
    if (!p) return;
    int *pi = p;

    *pi = 10;                /* effective type := int */
    sink_u((unsigned)*pi);   /* fine */

    *(double *)p = 2.5;      /* effective type := double -- `pi` is now stale */

    /* UB: `pi` still points at the object, but the object's effective type is
       `double` now.  "Changed at the wrong time" from pi's point of view. */
    printf("   stale *pi = %d   <-- UB\n", *pi);
    sink_u((unsigned)*pi);
    free(p);
}

static void case_15_3_retype_within_one_full_expression(void)
{
    BANNER("UB", "15.3: re-typing and reading inside a single full expression");

    void *p = malloc(sizeof(double));
    if (!p) return;
    int    *pi = p;
    double *pd = p;

    *pi = 3;
    /* The comma operator sequences the store before the read, but the read
       still uses the stale `int` lvalue after the object was re-typed to
       `double`.  Sequencing does not rescue you: 6.5p6 tracks the type, not
       the ordering. */
    int v = (*pd = 4.5, *pi);     /* UB */
    printf("   v = %d   <-- UB\n", v);
    sink_u((unsigned)v);
    free(p);
}

static void case_15_4_partial_overwrite_invalidates_the_whole(void)
{
    BANNER("UB", "15.4: a partial store re-types only SOME bytes, shredding the larger object");

    void *p = malloc(sizeof(double));
    if (!p) return;

    *(double *)p = 9.75;      /* bytes [0,sizeof(double)) have effective type double */
    *(int *)p    = 1;         /* bytes [0,sizeof(int)) are now `int`; the rest are
                                 still `double`-typed bytes.  There is no longer a
                                 whole `double` object there. */
    double d = *(double *)opaque(p);   /* UB: the leading bytes' effective type
                                          is int, not double. */
    printf("   d = %g   <-- UB\n", d);
    sink_d(d);
    free(p);
}

/* ================================================================== */
/* SECTION 16                                                         */
/* [UB] The effective type CAN change, but it is changed to a           */
/*      PROBLEMATIC type.                                               */
/* ================================================================== */

static void case_16_1_retype_beyond_the_allocation(void)
{
    BANNER("UB", "16.1: re-typing to a type larger than the allocated object");

    void *p = malloc(sizeof(int));     /* only sizeof(int) bytes exist */
    if (!p) return;

    /* R2 would happily make the effective type `long double`, but the store
       writes past the end of the allocated object: UB for a completely
       different reason (6.5.6p8 / 7.22.3p1). */
    *(long double *)opaque(p) = 1.0L;  /* heap overflow -- UB */
    printf("   wrote a long double into %zu bytes   <-- UB\n", sizeof(int));
    sink_d((double)*(long double *)p);
    free(p);
}

static void case_16_2_retype_at_a_misaligned_offset(void)
{
    BANNER("UB", "16.2: re-typing an interior, insufficiently aligned offset");

    unsigned char *raw = malloc(64);
    if (!raw) return;

    /* malloc's result is aligned for every fundamental type, but raw+1 is
       not.  Converting the pointer is already UB (6.3.2.3p7); the store would
       install `double` as the effective type but may fault or tear. */
    double *pd = (double *)opaque(raw + 1);
    *pd = 1.0;                                  /* UB */
    printf("   misaligned double = %g   <-- UB\n", *pd);
    sink_d(*pd);
    free(raw);
}

static void case_16_3_retype_to_a_type_with_trap_representations(void)
{
    BANNER("UB", "16.3: bytes typed by one type, then read as a type that may trap");

    void *p = malloc(sizeof(double) > sizeof(_Bool) ? sizeof(double) : sizeof(_Bool));
    if (!p) return;

    *(double *)p = -1.0;        /* effective type := double, bytes are a
                                   float pattern */
    /* Two problems at once: (a) 6.5p7 violation, and (b) even if you had used
       memcpy to dodge (a), `_Bool` has exactly two value representations, so
       an arbitrary byte is very likely a trap representation -> 6.2.6.1p5
       UB on read. */
    _Bool *pb = (_Bool *)opaque(p);
    printf("   as _Bool = %d   <-- UB\n", (int)*pb);
    sink_u((unsigned)*pb);
    free(p);
}

static void case_16_4_retype_pointer_to_integer_bytes(void)
{
    BANNER("UB", "16.4: object typed `void *`, then read as an integer type");

    void *p = malloc(sizeof(void *) > sizeof(uintptr_t) ? sizeof(void *) : sizeof(uintptr_t));
    if (!p) return;

    *(void **)p = p;                        /* effective type := void *      */
    uintptr_t *pu = (uintptr_t *)opaque(p); /* UB: uintptr_t is an integer
                                               type, never compatible with a
                                               pointer type, even when the
                                               sizes match. */
    printf("   as uintptr_t = %ju   <-- UB\n", (uintmax_t)*pu);
    sink_u((unsigned long long)*pu);
    free(p);
}

static void case_16_5_retype_to_a_const_qualified_incompatible_type(void)
{
    BANNER("UB", "16.5: writing through a type that is not a *qualified version* but a different type");

    void *p = malloc(sizeof(long));
    if (!p) return;
    *(long *)p = 1;                   /* effective type := long */

    /* `const long *` IS a qualified version -> legal to read through. */
    const long *ok = p;
    sink_u((unsigned long long)*ok);
    printf("   const long read is fine: %ld\n", *ok);

    /* `unsigned long *` IS the corresponding unsigned type -> also legal. */
    unsigned long *ok2 = p;
    printf("   unsigned long read is fine: %lu\n", *ok2);

    /* `long long *` is a DIFFERENT type, even if it happens to be the same
       width on this implementation. */
    long long *bad = (long long *)opaque(p);
    printf("   long long read = %lld   <-- UB\n", *bad);
    sink_u((unsigned long long)*bad);
    free(p);
}

/* ================================================================== */
/* SECTION 17                                                         */
/* [UB] R3 subtleties: copying from a source that has NO effective      */
/*      type, and copying only part of an object.                       */
/* ================================================================== */

static void case_17_1_memcpy_from_an_untyped_source(void)
{
    BANNER("UB", "17.1: R3's 'if it has one' -- copying from an object with no effective type");

    void *src = malloc(sizeof(int));
    void *dst = malloc(sizeof(int));
    if (!src || !dst) { free(src); free(dst); return; }

    /* `src` was never stored into through a non-character lvalue, so it has
       no effective type.  R3's trailing clause "if it has one" therefore does
       not apply, and `dst` gets no effective type either -- it falls back to
       R4 for the *access*.  The real problem is that we are reading
       indeterminate bytes, which is UB (6.2.4p6 / 6.7.9p10, and J.2). */
    memcpy(dst, src, sizeof(int));
    printf("   *(int*)dst = %d   <-- UB: indeterminate value\n", *(int *)dst);
    sink_u((unsigned)*(int *)dst);
    free(src); free(dst);
}

static void case_17_2_partial_memcpy_leaves_a_hybrid(void)
{
    BANNER("UB", "17.2: copying only part of an object produces a half-typed object");

    double whole = 1.5;
    void  *dst   = malloc(sizeof(double));
    if (!dst) return;

    *(double *)dst = 2.5;              /* effective type := double */
    memcpy(dst, &whole, sizeof(double) / 2);  /* only the first half is
                                                 re-typed from the source */
    /* The object is now a chimera: no complete `double` lives there, so
       reading it as a double is UB (and the value would be nonsense anyway on
       many ABIs). */
    printf("   hybrid double = %g   <-- UB\n", *(double *)opaque(dst));
    sink_d(*(double *)dst);
    free(dst);
}

/* ================================================================== */
/* SECTION 18                                                         */
/* [UB] No effective type was ever installed, but the operation         */
/*      performed requires a determinate value.                         */
/* ================================================================== */

static void case_18_1_read_indeterminate_malloc_bytes(void)
{
    BANNER("UB", "18.1: R4 permits the lvalue type, but the VALUE is indeterminate");

    void *p = malloc(sizeof(int));
    if (!p) return;

    /* 6.5p6 R4 says the effective type for this access is simply `int`, so
       6.5p7 is satisfied -- there is no aliasing violation here at all.
       The UB comes from elsewhere: malloc'd storage has an indeterminate
       value (7.22.3.4p2), and using an indeterminate value is UB whenever the
       object could have been declared with a register storage class or the
       bytes are a trap representation (6.3.2.1p2, 6.2.6.1p5, J.2). */
    int v = *(int *)p;
    printf("   uninitialized int = %d   <-- UB: indeterminate value\n", v);
    sink_u((unsigned)v);
    free(p);
}

static void case_18_2_read_indeterminate_then_branch(void)
{
    BANNER("UB", "18.2: branching on an indeterminate value (classic 'unstable value')");

    void *p = malloc(sizeof(int));
    if (!p) return;
    int v = *(int *)p;
    /* Because the value is indeterminate, the compiler may evaluate `v`
       differently at each use; both branches (or neither) may appear to run. */
    if (v == v)
        printf("   v == v was true    <-- UB: nothing is guaranteed\n");
    else
        printf("   v == v was FALSE!  <-- UB: nothing is guaranteed\n");
    sink_u((unsigned)v);
    free(p);
}

/* ================================================================== */
/* SECTION 19                                                         */
/* [UB] Qualification/atomicity mismatches that 6.5p7 does NOT forgive. */
/*      6.5p7 permits "a qualified version OF the effective type" --    */
/*      that direction only.  Dropping a qualifier is a different rule. */
/* ================================================================== */

static volatile int g_volatile = 1;

static void case_19_1_volatile_object_via_nonvolatile_lvalue(void)
{
    BANNER("UB", "19.1: object declared `volatile int`, accessed through a plain `int` lvalue");

    int *p = (int *)(uintptr_t)opaque((void *)(uintptr_t)&g_volatile);
    *p = 2;     /* UB twice over:
                   (a) 6.7.3p6 -- referring to a volatile-defined object
                       through a non-volatile-qualified lvalue is UB; and
                   (b) 6.5p7 -- `int` is not compatible with `volatile int`
                       (6.7.3p10 requires identical qualifiers), nor is it a
                       *qualified version* of it.  The allowance runs the
                       other way: a `volatile int *` may access an `int`. */
    printf("   g_volatile = %d   <-- UB\n", g_volatile);
    sink_u((unsigned)g_volatile);
}

#ifndef __STDC_NO_ATOMICS__
#include <stdatomic.h>
static _Atomic int g_atomic = 1;

static void case_19_2_atomic_object_via_nonatomic_lvalue(void)
{
    BANNER("UB", "19.2: object declared `_Atomic int`, accessed through a plain `int` lvalue");

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
static void case_19_2_atomic_object_via_nonatomic_lvalue(void)
{
    BANNER("UB", "19.2: skipped -- no atomics on this implementation");
}
#endif

/* ================================================================== */
/* SECTION 20                                                         */
/* [UB] Effective types agree PERFECTLY and the access is still UB,     */
/*      because `restrict` is an orthogonal promise (6.7.3.1).          */
/* ================================================================== */

static int case_20_helper(int *restrict a, int *restrict b)
{
    *a = 1;
    *b = 2;      /* the programmer has promised `b` does not alias `a` */
    return *a;   /* the compiler may fold this to 1 */
}

static void case_20_1_restrict_violation_with_matching_types(void)
{
    BANNER("UB", "20.1: identical effective types, but a `restrict` promise is broken");

    int x = 0;
    int *p = opaque(&x);
    int r = case_20_helper(p, p);     /* UB: both parameters are restrict-qualified
                                   and designate the same object, yet both are
                                   used to modify it.  6.5p6/p7 are entirely
                                   satisfied -- the effective type is `int` on
                                   every access.  Aliasing UB is not only
                                   about types. */
    printf("   returned %d (compiler may say 1, memory says 2)   <-- UB\n", r);
    sink_u((unsigned)r);
}

/* ================================================================== */
/* SECTION 21                                                         */
/* [UB] The object is gone: lifetime, not type, is the problem.         */
/* ================================================================== */

static int *g_dangling_auto;

static void case_21_stash_local(void)
{
    int local = 7;
    g_dangling_auto = opaque(&local);   /* escapes its lifetime */
}

static void case_21_1_use_a_freed_pointer_VALUE(void)
{
    BANNER("UB", "21.1: even READING a freed pointer's value is UB (not just dereferencing)");

    int *p = malloc(sizeof(int));
    if (!p) return;
    *p = 1;
    free(p);

    /* 6.2.4p2 / J.2: the value of a pointer becomes INDETERMINATE when the
       object it points to reaches the end of its lifetime.  Printing or
       comparing `p` -- without any dereference at all -- is already UB. */
    printf("   freed pointer value = %p   <-- UB\n", (void *)p);
    if (p != NULL) sink_p(p);
}

static void case_21_2_dangling_automatic_object(void)
{
    BANNER("UB", "21.2: dereferencing a pointer to an automatic object whose block exited");

    case_21_stash_local();
    /* The object no longer exists, so it has no effective type to speak of;
       6.5p6 never gets a chance to apply. */
    printf("   *g_dangling_auto = %d   <-- UB\n", *g_dangling_auto);
    sink_u((unsigned)*g_dangling_auto);
}

struct wrap { int a[4]; };
static struct wrap case_21_make(void) { struct wrap w = { { 1, 2, 3, 4 } }; return w; }

static void case_21_3_temporary_lifetime_object(void)
{
    BANNER("UB", "21.3: objects with TEMPORARY lifetime (6.2.4p8)");

    /* A non-lvalue structure containing an array member creates an object
       with temporary lifetime.  Its lifetime ends at the end of the full
       expression, and -- note -- any attempt to MODIFY it is UB even while
       it is alive. */
    const int *p = case_21_make().a;     /* lifetime ends at this semicolon */
    printf("   p[0] after the full expression = %d   <-- UB\n", p[0]);
    sink_u((unsigned)p[0]);
}

/* ================================================================== */
/* SECTION 22                                                         */
/* [UB] Declared objects that may not be modified at all.               */
/* ================================================================== */

static void case_22_1_modify_a_const_object(void)
{
    BANNER("UB", "22.1: modifying an object whose declared type is const-qualified");

    const int n = 1;
    const int *cp = &n;
    int *p = (int *)(uintptr_t)opaque((void *)(uintptr_t)cp);
    *p = 2;                 /* UB: 6.7.3p6.  Note the effective type is
                               `const int`; stripping the qualifier from the
                               POINTER does not strip it from the OBJECT, and
                               R1 keeps the object's type fixed. */
    printf("   n = %d   <-- UB\n", n);
    sink_u((unsigned)n);
}

static void case_22_2_modify_a_string_literal(void)
{
    BANNER("UB", "22.2: modifying a string literal (declared type char[N])");

    char *s = (char *)opaque((void *)"hello");
    s[0] = 'H';             /* UB: 6.4.5p7.  The literal's declared type is
                               char[6], so a `char` lvalue is type-correct --
                               the UB is the modification itself, not an
                               effective-type violation. */
    printf("   %s   <-- UB\n", s);
    sink_p(s);
}

/* ================================================================== */
/* Driver                                                              */
/* ================================================================== */

static void run_defined(void)
{
    puts("###########################################################");
    puts("# WELL-DEFINED CASES                                      #");
    puts("###########################################################");

    puts("\n--- 1. Effective type defined (declared) and unchangeable; correct access ---");
    case_1_1_declared_type_accessed_as_itself();
    case_1_2_qualified_and_signedness_variants();
    case_1_3_aggregate_containing_the_type();

    puts("\n--- 2. Effective type unchangeable, but character access is always legal ---");
    case_2_1_inspect_any_object_as_bytes();
    case_2_2_memcpy_out_of_a_declared_object();
    case_2_3_union_punning();

    puts("\n--- 3. No declared type: a store installs the effective type (R2) ---");
    case_3_1_malloc_store_then_read();
    case_3_2_effective_type_survives_nonmodifying_accesses();
    case_3_3_struct_effective_type_then_member_access();

    puts("\n--- 4. No declared type: the effective type may be changed repeatedly ---");
    case_4_1_change_effective_type_repeatedly();
    case_4_2_retype_after_free_and_realloc();

    puts("\n--- 5. R3: memcpy / character-array copy propagates the source's type ---");
    case_5_1_memcpy_propagates_effective_type();
    case_5_2_character_array_copy_propagates();
    case_5_3_memcpy_allocated_to_allocated();

    puts("\n--- 6. R4: no effective type at all -> the lvalue's type is used ---");
    case_6_1_fresh_malloc_write_is_always_legal();
    case_6_2_character_store_does_NOT_install_a_type();
    case_6_3_calloc_then_read_as_unsigned();

    puts("\n--- 7. Lifetimes: objects begin and end, and so do their effective types ---");
    case_7_1_free_then_malloc_resets_everything();
    case_7_2_automatic_storage_reuse_across_blocks();
    case_7_3_compound_literals_have_a_declared_type();
    case_7_4_vla_has_a_declared_type();

    puts("\n--- 8. Structural escape hatches: common initial sequence, first-member casts ---");
    case_8_1_common_initial_sequence();
    case_8_2_first_member_upcast();

    puts("\n--- 9. Implementation-defined compatibility and the three character types ---");
    case_9_1_enum_vs_its_compatible_integer_type();
    case_9_2_the_three_character_types();

    puts("\n--- 10. Flexible array members, padding bytes, memset ---");
    case_10_1_flexible_array_member();
    case_10_2_padding_bytes();
    case_10_3_memset_does_not_install_a_type();

    puts("\n--- 11. How to type-pun without violating 6.5p7 ---");
    case_11_1_escape_hatches();
}

static void run_undefined(void)
{
    puts("\n###########################################################");
    puts("# UNDEFINED-BEHAVIOR CASES  (output below proves nothing)  #");
    puts("###########################################################");

    puts("\n--- 12. Effective type fixed by R1; access through a forbidden lvalue type ---");
    case_12_1_read_int_as_float();
    case_12_2_write_int_through_short();
    case_12_3_struct_pun_between_layout_compatible_types();
    case_12_4_char_array_used_as_int_storage();
    case_12_5_alignment_of_declared_char_buffer();

    puts("\n--- 13. Trying to CHANGE an effective type that R1 has pinned ---");
    case_13_1_memcpy_cannot_retype_a_declared_object();
    case_13_2_store_does_not_retype_automatic_storage();
    case_13_3_reuse_of_a_declared_struct_as_another_struct();

    puts("\n--- 14. Effective type installed on allocated storage; incompatible access ---");
    case_14_1_installed_int_read_as_float();
    case_14_2_installed_struct_read_as_unrelated_struct();
    case_14_3_memcpy_installed_type_then_wrong_read();

    puts("\n--- 15. Re-typing is allowed, but it happens at the WRONG TIME ---");
    case_15_1_read_before_the_retyping_store();
    case_15_2_interleaved_accesses_across_a_call();
    case_15_3_retype_within_one_full_expression();
    case_15_4_partial_overwrite_invalidates_the_whole();

    puts("\n--- 16. Re-typing is allowed, but to a PROBLEMATIC type ---");
    case_16_1_retype_beyond_the_allocation();
    case_16_2_retype_at_a_misaligned_offset();
    case_16_3_retype_to_a_type_with_trap_representations();
    case_16_4_retype_pointer_to_integer_bytes();
    case_16_5_retype_to_a_const_qualified_incompatible_type();

    puts("\n--- 17. R3 subtleties: untyped sources and partial copies ---");
    case_17_1_memcpy_from_an_untyped_source();
    case_17_2_partial_memcpy_leaves_a_hybrid();

    puts("\n--- 18. No effective type, but a determinate value was required ---");
    case_18_1_read_indeterminate_malloc_bytes();
    case_18_2_read_indeterminate_then_branch();

    puts("\n--- 19. Qualifier / atomicity mismatches that 6.5p7 does NOT forgive ---");
    case_19_1_volatile_object_via_nonvolatile_lvalue();
    case_19_2_atomic_object_via_nonatomic_lvalue();

    puts("\n--- 20. Matching effective types, broken `restrict` promise ---");
    case_20_1_restrict_violation_with_matching_types();

    puts("\n--- 21. The object is gone: lifetime, not type, is the problem ---");
    case_21_1_use_a_freed_pointer_VALUE();
    case_21_2_dangling_automatic_object();
    case_21_3_temporary_lifetime_object();

    puts("\n--- 22. Declared objects that may not be modified at all ---");
    case_22_1_modify_a_const_object();
    case_22_2_modify_a_string_literal();
}

int main(int argc, char **argv)
{
    /* Unbuffered: if a UB case crashes, we still see how far we got. */
    setvbuf(stdout, NULL, _IONBF, 0);

    run_defined();

    if (argc > 1 && strcmp(argv[1], "ub") == 0)
        run_undefined();
    else
        puts("\n(Pass \"ub\" on the command line to also execute the "
             "undefined-behavior cases.)");

    sink_u(0);
    return 0;
}
