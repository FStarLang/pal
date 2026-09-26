#include "pal.h"
#include <stdlib.h>
#include <stdint.h>

/* Acceptance test 1 from `palow.md`: "`malloc` is no longer a special
   built-in; we can give a spec to a custom `xmalloc` function and use it just
   like `malloc` today."

   Under the old model `malloc` had to be a built-in, because a block's
   ownership predicate names the type stored in it and only the emitter --
   pattern-matching `malloc(sizeof(T))` -- knew what that type was. A function
   the user wrote could not be given the same contract, because there was no
   way to say "this hands back storage of type `T`" without the emitter's help.

   Palow's `malloc` hands back *bytes*, and the caller claims them at whatever
   type it likes, so the contract a custom allocator needs is one a user can
   write. That is what this test is: an allocator and a deallocator that are
   ordinary C functions with ordinary annotations, and a client that never
   names `malloc` or `free` at all. Nothing below is a translator special
   case. */

typedef struct {
    uint32_t used;
    uint32_t cap;
} slot;

/* `_nullable` says the allocation may have failed, which is the honest
   contract for a constructor; see `test/malloc` for why the old model cannot
   state it. The non-nullable name is what the functions taking an existing
   block are written against. */
#ifdef PALOW
_allocated _nullable typedef slot *slot_optr;
#else
_allocated typedef slot *slot_optr;
#endif
_allocated typedef slot *slot_ptr;

/* The allocator. Its postcondition is the one a caller wants: a block, the
   right to free it, and an initialised object in it. */
slot_optr xmalloc_slot(uint32_t cap)
    _ensures((_specint) return->cap == cap)
    _ensures((_specint) return->used == 0)
{
#ifdef PALOW
    slot *p = malloc(sizeof(slot));
    if (p == NULL) {
        return NULL;
    }
#else
    slot *p = malloc(sizeof(slot));
#endif
    *p = (slot) { .used = 0, .cap = cap };
    return p;
}

/* And the matching deallocator. `_consumes` spends the caller's ownership and
   the right to free, which is exactly what `free` itself takes -- so a
   `slot_ptr` cannot be freed twice, and a client that calls this never has to
   mention `free`. */
void xfree_slot(_consumes slot_ptr p)
{
    free(p);
}

/* A client written entirely against the custom pair. */
uint32_t xmalloc_client(uint32_t cap)
    _ensures(return == 0)
{
    slot_optr p = xmalloc_slot(cap);
#ifdef PALOW
    if (p == NULL) {
        return 0;
    }
#endif
    uint32_t used = p->used;
    xfree_slot(p);
    return used;
}
