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

// An *optional* pointer to const. The permission and pointee become
// signature-level implicits like those of any const parameter, but they sit
// behind a null guard.
void read_optional(PCINT _nullable p) {}

// A null argument has no hold of its own to solve those implicits against. The
// ghost steps test/nullable describes for any null argument supply one, so the
// call elaborates.
void call_read_optional(void)
{
    _ghost_stmt(Pulse.Lib.C.Nullable.intro_unless_null_null (null #Int32.t) (Pulse.Lib.Reference.pts_to (null #Int32.t) #1.0R 0l));
    read_optional(NULL);
    _ghost_stmt(Pulse.Lib.C.Nullable.elim_unless_null_null (null #Int32.t) _);
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
