// Regression test: an initializer list shorter than the array it initializes.
//
// C11 6.7.9p21 zero-initializes the elements an initializer list does not
// reach, and an array's length comes from its type rather than from the list.
// The translation used to build an array literal with exactly as many elements
// as the list had, so `uint8_t bytes[16] = {0}` produced a `uint8_t[1]` that
// then failed to convert to `uint8_t[16]`. That made the extremely common
// `T x = {0}` idiom untranslatable for any aggregate containing an array, and
// because the `admit()` placeholder left behind is not valid Pulse in an
// expression position, the enclosing module was lost to a syntax error rather
// than to a reported translation failure.
//
// Covers, for the arrays embedded in a struct value:
//   1. `{0}` on a struct whose field is an array (the shape of a GUID/UUID).
//   2. A partial list: written prefix, zeroed tail.
//   3. A nested array of arrays, where padding an outer element has to
//      synthesize a zeroed inner array rather than a scalar zero.
//   4. An array of structs, where padding has to synthesize a struct value.
//   5. A complete list, which must still round-trip unchanged.
//
// Fixed-size arrays declared as *locals* are not covered: assigning an
// initializer to one is a separate, pre-existing gap (the assignment does not
// re-establish the element ownership that the stack allocation gave up), and
// it fails the same way for a complete list.

#include "pal.h"
#include <stdint.h>

typedef struct guid {
    uint8_t bytes[16];
} guid;

typedef struct pair {
    uint32_t lo;
    uint32_t hi;
} pair;

typedef struct grid {
    uint32_t cells[3][4];
} grid;

typedef struct pairs {
    pair entries[4];
} pairs;

typedef struct quad {
    uint8_t bytes[4];
} quad;

/* 1. `{0}` on a struct whose only field is an array. */
guid zeroed_bytes(void)
{
    guid g = {0};
    return g;
}

/* 2. A written prefix with a zeroed tail. */
guid partial_bytes(void)
{
    guid g = {{7, 9}};
    return g;
}

/* 3. Array of arrays: padding an outer element yields a zeroed inner array. */
grid partial_cells(void)
{
    grid g = {{{1, 2}}};
    return g;
}

/* 4. Array of structs: padding yields the struct's default. */
pairs partial_entries(void)
{
    pairs p = {{{1, 2}}};
    return p;
}

/* 5. A complete list is unaffected. */
quad full_list(void)
{
    quad q = {{0, 1, 2, 3}};
    return q;
}
