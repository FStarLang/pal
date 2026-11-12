#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* A typedef whose tag differs from the typedef name, used in a compound
   literal inside a contract. The body translation resolves the typedef to its
   tag; the contract must do the same. */
typedef struct _handle {
    uintptr_t Value;
} handle;

#define HANDLE_NULL ((handle){.Value = 0})
#define HANDLE_IS_NULL(H) ((H).Value == HANDLE_NULL.Value)

int *handle_ptr(handle h)
    _ensures(HANDLE_IS_NULL(h) || return != NULL);

int *from_handle(handle h)
    _ensures(HANDLE_IS_NULL(h) || return != NULL)
{
    int *p = NULL;
    if (!HANDLE_IS_NULL(h)) {
        p = handle_ptr(h);
        _assert(p != NULL);
    }
    return p;
}
