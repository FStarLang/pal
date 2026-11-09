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

// An *optional* pointer to const, marked `_mutable`: the declaration opts out
// of the const reading, so the parameter is held at full permission like any
// mutable one rather than borrowed at a signature-level fraction.
void read_optional(PCINT _nullable _mutable p)
{
    if (p != NULL)
    {
        int seen = *p;
        _assert(seen == *p);
    }
}

// PAL writes down the ghost steps both calls need: taking a supplied
// argument's hold back out of the guard, and introducing the guard -- at full
// permission and a zero value, which pins the signature's implicits -- for a
// null one.
void call_read_optional()
{
    int x = 67;
    read_optional(&x);
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
