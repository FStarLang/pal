#include "pal.h"
#include <stdint.h>

/* `q` holds the address of the `seq` that `h->s` points at when `q` is set.
   `swap` may store another pointer in `h->s`, after which `*q` is no longer
   `h->s->seq`; reading the alias as that place would be unsound. */

struct slab { uint32_t seq; uint32_t state; };
struct holder { struct slab *s; };

void swap(struct holder *a, struct holder *b);

void stale(struct holder *h, struct holder *g)
{
    uint32_t *q = &h->s->seq;
    swap(h, g);
    *q = 5;
}
