#include "pal.h"
#include <stddef.h>

// A pointer-to-const spelled through a typedef, the way a codebase spells every one
// of its read-only parameters. The `const` is hidden behind the typedef, so it
// is only visible on the canonical type; recognizing it there is what lets the
// contract below preserve the caller's hold instead of re-establishing it.
typedef const int* PCINT;

int read_through_typedef(PCINT p)
    _ensures(return == *p)
{
    return *p;
}

// An *optional* pointer to const, marked `_mutable`. The permission and
// pointee must not become signature-level implicits here: under `_nullable`
// the hold sits behind a null guard, so a call site that passes a literal null
// offers nothing to solve them against and the call would not elaborate.
// `_mutable` asks for the quantified treatment instead, which is what makes
// the null call site below translate at all. Const-ness alone is not enough to
// decide this -- an optional const input with no null call site is better off
// const -- so it is the declaration that says which it wants.
void read_optional(PCINT _nullable _mutable p)
{
    if (p != NULL)
    {
        int seen = *p;
        _assert(seen == *p);
    }
}

void call_read_optional()
{
    int x = 67;
    read_optional(&x);
    // The point of this call is that it elaborates at all: a null argument has
    // no hold to unify a signature-level permission or value against, so an
    // optional pointer must not put either in the signature.
    read_optional(NULL);
}

int call_read_through_typedef()
{
    int x = 67;
    int first = read_through_typedef(&x);
    // Had the callee re-existentialized `*p`, this second call would start
    // from a value the caller no longer knows anything about, and the
    // assertion below could not be proved.
    int second = read_through_typedef(&x);
    _assert(first == 67 && second == 67 && x == 67);
    return first + second;
}
