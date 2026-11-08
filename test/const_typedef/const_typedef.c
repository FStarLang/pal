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

// A null argument still has no hold of its own to solve the parameter's value
// implicit against -- under Palow even a mutable optional parameter names its
// pointee value in the signature -- so the ghost steps test/nullable describes
// for any null argument supply one.
void call_read_optional()
{
    int x = 67;
    // A supplied argument's hold comes back wrapped in the guard; knowing the
    // address is not null takes it back out.
    _ghost_stmt(int32_t_pts_to_not_null $&(x));
    read_optional(&x);
    _ghost_stmt(elim_unless_null $&(x) _);
    _ghost_stmt(intro_unless_null_null null (int32_t_pts_to null 1.0R 0l));
    read_optional(NULL);
    _ghost_stmt(elim_unless_null_null null _);
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
