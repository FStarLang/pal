#include "pal.h"
#include <stdint.h>

/* Specifications use mathematical arithmetic. Explicit casts state the
   modular invariant of the C counter, including the total < next case. */
void wrapped_batch(uint16_t total, uint16_t next)
{
    uint16_t count = total - next;
    if (count > 4) {
        count = 4;
    }
    uint16_t index = next;
    for (uint16_t i = 0; i < count; i++)
        _invariant(_live(i) && _live(index) && _live(count))
        _invariant(i <= count && count <= 4)
        _invariant(count <= (uint16_t)(total - next))
        _invariant(index == (uint16_t)(next + i))
    {
        index++;
    }
}

/* With ordering established, the mathematical version is also valid. */
void ordered_batch(uint16_t total, uint16_t next)
    _requires(next <= total)
{
    uint16_t count = total - next;
    if (count > 4) {
        count = 4;
    }
    uint16_t index = next;
    for (uint16_t i = 0; i < count; i++)
        _invariant(_live(i) && _live(index) && _live(count))
        _invariant(i <= count && count <= 4)
        _invariant(count <= total - next)
        _invariant(index == next + i)
    {
        index++;
    }
}
