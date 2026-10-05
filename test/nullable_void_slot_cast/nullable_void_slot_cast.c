#include "pal.h"
#include <stdint.h>
#include <stddef.h>

// An optional out slot: callers that do not want the pointer pass NULL.
int acquire_opt(_nullable void** out);

// A typed slot cast to the optional `void **`. It is handed to the callee as
// the void* cell it expects, under the callee's `unless_null` guard; that
// guard has to be eliminated before the cell is handed back as the typed slot.
int get_local(void)
{
    _arrayptr uint64_t* entries = NULL;
    int s = acquire_opt((void**)&entries);
    return s;
}

// The same with a plain pointer slot.
int get_local_ptr(void)
{
    uint64_t* entry = NULL;
    int s = acquire_opt((void**)&entry);
    return s;
}

// Declining the optional output still works.
int decline(void)
{
    int s = acquire_opt(NULL);
    return s;
}
