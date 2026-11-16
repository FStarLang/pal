#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* A NULL result must stay NULL: `q == NULL` cannot be read as false just
   because a non-NULL result would be the place. */

struct inner { uint32_t a; uint32_t b; };
struct ctx { struct inner in; uint32_t has; };
struct req { struct ctx *c; uint32_t k; };

struct inner *get_lead(struct req *r)
    _ensures(return == NULL || return == &r->c->in);

void claims_non_null(struct req *r)
{
    struct inner *q = get_lead(r);
    _assert(q != NULL);
}
