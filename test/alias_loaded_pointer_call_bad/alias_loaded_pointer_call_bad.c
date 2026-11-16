#include "pal.h"
#include <stdint.h>

/* The store through `q` happens after the call on the right-hand side, which
   may change `h->s`. */

struct slab { uint32_t seq; uint32_t state; };
struct holder { struct slab *s; };

uint32_t swap_get(struct holder *a, struct holder *b);

void stale_store(struct holder *h, struct holder *g)
{
    uint32_t *q = &h->s->seq;
    *q = swap_get(h, g);
}
