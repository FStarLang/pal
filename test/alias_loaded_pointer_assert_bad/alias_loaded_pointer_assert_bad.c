#include "pal.h"
#include <stdint.h>

/* An assertion reads the alias's place as much as code does. After `swap`
   may have stored another pointer in `h->s`, `*q` is the old slab's `seq`,
   not `h->s->seq`, so the assertion is false in C. */

struct slab { uint32_t seq; uint32_t state; };
struct holder { struct slab *s; };

void swap(struct holder *a, struct holder *b);

void stale_assert(struct holder *h, struct holder *g)
{
    uint32_t *q = &h->s->seq;
    *q = 5;
    h->s->seq = 5;
    swap(h, g);
    _assert(*q == h->s->seq);
}
