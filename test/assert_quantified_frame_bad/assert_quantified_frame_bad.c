#include "pal.h"
#include <stddef.h>
#include <stdint.h>

void quantified_frame_bad(_array const uint32_t *p)
    _requires(p._length > 0)
    _requires(_forall(size_t i, i < p._length ==> p[i] == 7))
{
    _assert(_forall(size_t i, i < p._length ==> p[i] == 8));
}
