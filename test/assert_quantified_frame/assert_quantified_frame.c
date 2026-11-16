#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* Exercise the spec-only assertion frame independently of array suffix
   lending, which is not involved in this merge's assertion changes. */
void quantified_frame(_array const uint32_t *p)
    _requires(p._length > 0)
    _requires(_forall(size_t i, i < p._length ==> p[i] == 7))
{
    _assert(p._length > 0);
    _assert(_forall(size_t i, i < p._length ==> p[i] == 7));
}
