#include "pal.h"
#include <stdint.h>
#include <stddef.h>

// An optional out slot whose contract states the guarded resource itself
// (`_plain`), so PAL adds no default `unless_null` guard of its own.
int acquire_plain(_nullable _plain void** out)
    _requires(_inline_pulse(
        Pulse.Lib.C.Nullable.unless_null $(out) (Pulse.Lib.Reference.pts_to_uninit $(out))))
    _ensures(_inline_pulse(
        Pulse.Lib.C.Nullable.unless_null $(out)
            (exists* v. Pulse.Lib.Reference.pts_to $(out) v)));

// A typed slot cast to the optional `void **`.
int get_local(void)
{
    _arrayptr uint64_t* entries = NULL;
    int s = acquire_plain((void**)&entries);
    return s;
}

// Declining the optional output.
int decline(void)
{
    int s = acquire_plain(NULL);
    return s;
}
