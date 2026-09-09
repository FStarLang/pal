// A `goto` target that is followed by more code has to say what holds when it
// is reached: Pulse writes a forward jump as a block carrying a postcondition
// followed by a label, and has no syntax for an unannotated label in the
// middle of a block. Without `_ensures` the generated module does not parse,
// and F* then reports a syntax error at the enclosing function instead of at
// the label, so PAL diagnoses the missing annotation itself.
//
// This test only translates; see `verify` in the Makefile. `goto_fail` covers
// the two shapes that do work: an annotated label with code after it, and a
// bare label at the very end of a function.

#include "pal.h"

int missing_label_ensures(int *p)
{
    if (*p != 0)
        goto fail;
    *p = 42;
fail:;
    return 1;
}
