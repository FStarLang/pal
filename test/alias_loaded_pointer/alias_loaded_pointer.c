#include "pal.h"
#include <stdint.h>

/* An alias whose place reads a pointer out of memory stands for the place
   that pointer held when the alias was bound. A callee that says it leaves
   the pointer alone keeps the alias usable. */

struct slab { uint32_t seq; uint32_t state; };
struct holder { struct slab *s; };

void keep(struct holder *h)
    _ensures(h->s == _old(h->s));

uint32_t next(struct holder *h)
    _ensures(h->s == _old(h->s));

void across_call(struct holder *h)
{
    uint32_t *q = &h->s->seq;
    *q = 1;
    keep(h);
    *q = 5;
    _assert(h->s->seq == 5);
    _assert(*q == h->s->seq);
}

void store_call_result(struct holder *h)
{
    uint32_t *q = &h->s->seq;
    *q = next(h);
}

void copies(struct holder *h)
{
    uint32_t *q = &h->s->seq;
    uint32_t *r = q;
    *q = 1;
    *r = *q + 1;
    _assert(h->s->seq == 2);
}
