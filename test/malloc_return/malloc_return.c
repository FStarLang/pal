#include "pal.h"
#include <stdlib.h>

/* Returning a block that the allocation may have failed to produce.

   `_nullable` on a return type is stated the same way in both models -- the
   callee's `ensures` puts the whole grant under a nullness guard -- but only
   Palow's emitter spends that guard at a call site, so under PAL's current
   emitter the caller cannot reach the block at all. The divergence is recorded
   here rather than worked around: the non-Palow arm keeps the older shape, in
   which the allocation is assumed to succeed. */
#ifdef PALOW

typedef int *int_ptr _allocated _nullable;

int_ptr alloc_int() {
    int *p = (int *) malloc(sizeof(int));
    if (p == NULL) {
        return NULL;
    }
    *p = 0;
    return p;
}

int alloc_and_free(int x) {
    int_ptr p = alloc_int();
    if (p == NULL) {
        return 0;
    }
    free(p);
    return 42;
}

#else

typedef int *int_ptr _allocated;

int_ptr alloc_int() {
    int *p = (int *) malloc(sizeof(int));
    *p = 0;
    return p;
}

int alloc_and_free(int x) {
    free(alloc_int());
    return 42;
}

#endif
