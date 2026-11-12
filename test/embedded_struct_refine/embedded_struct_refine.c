// A struct whose declaration's `_refine` relates its owned array to a count,
// embedded by value in another struct. Every contract that holds the
// container states the embedded invariant at the field, so a callee that
// takes the embedded struct gets it, and the container type is not reported
// as weakened.
#include "pal.h"
#include <stdint.h>

typedef struct _D { uint32_t x; } D;

_refine(this.Arr._length == this.Count)
typedef struct _IT { _array D *Arr; uint32_t Count; } IT;

typedef struct _CTX { uint32_t a; IT It; } CTX;

uint32_t first_or_zero(IT *it)
{
    if (it->Count == 0) {
        return 0;
    }
    return it->Arr[0].x;
}

uint32_t ctx_first(CTX *c)
{
    return first_or_zero(&c->It);
}

uint32_t ctx_count(CTX *c)
{
    return c->It.Count;
}
