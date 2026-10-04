#include "pal.h"
#include <stdint.h>
#include <stddef.h>

// An acquire-style interface writes an untyped pointer into the caller's slot.
int acquire(void** out);

// A typed wrapper whose out slot holds an array pointer. It fills the slot
// through a (void**) cast, so the array slot must be passed as the void* cell
// the callee expects, and handed back as an array slot afterwards.
int get_table(_arrayptr uint64_t** out)
{
    int s = acquire((void**)out);
    return s;
}

// The cast also works for a local array slot.
int get_local(void)
{
    _arrayptr uint64_t* entries = NULL;
    int s = acquire((void**)&entries);
    return s;
}

// A caller passes the address of its own array slot to the typed wrapper.
int use_table(void)
{
    _arrayptr uint64_t* entries = NULL;
    int s = get_table(&entries);
    return s;
}
