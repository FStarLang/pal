#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* `_assert(p != NULL)` on a parameter whose pointee the contract grants:
   the points-to says the pointer is not null, and the assertion is proved
   from it. */

struct s { uint32_t n; };
union __attribute__((annotate("pal-overlay"))) u { uint32_t a; struct s b; };

uint32_t to_struct(struct s *p)
{
    _assert(p != NULL);
    return p->n;
}

void to_union(union u *p)
{
    _assert(p != NULL);
}

uint32_t to_scalar(uint32_t *p, struct s *q)
{
    _assert(p != NULL && q != NULL);
    return *p + 0 * q->n;
}
