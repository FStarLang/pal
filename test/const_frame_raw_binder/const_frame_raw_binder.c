#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

/* A legacy hand-written invariant names the sequence binder directly.
   The const frame's fixed resource key must not leave that name unbound. */
void unchanged_array(_array const uint32_t *p, uint32_t n)
    _requires(n <= p._length)
{
    uint32_t i = 0;
    while (i < n)
        _invariant(_live(i))
        _invariant(i <= n)
        _invariant((bool)_inline_pulse(inv_val_p == FStar.Ghost.reveal val_p))
    {
        i++;
    }
}
