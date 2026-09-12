#include "pal.h"
#include <stdint.h>

/*
 * A local has an address, and in C that address is never NULL. Pulse does not
 * get that for free -- the cell is a `ref`, and `ref` includes `null` -- so PAL
 * states it at the declaration.
 *
 * Without that, a callee whose contract says its out-parameter is non-null is
 * uncallable on `&local`: the caller would have to establish the non-nullness
 * itself, at every call, for every local.
 */

void
store(int32_t *Out)
    _requires(Out != 0);

void
caller(void)
{
    int32_t x;

    x = 0;
    store(&x);
}
