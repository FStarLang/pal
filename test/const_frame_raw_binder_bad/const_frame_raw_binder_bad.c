#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

void impossible(_array const uint32_t *p, uint32_t n)
    _requires(n <= p._length)
{
    uint32_t i = 0;
    while (i < n)
        _invariant(_live(i))
        _invariant(i <= n)
        _invariant((bool)_inline_pulse(FStar.Seq.length inv_val_p < 0))
    {
        i++;
    }
}
