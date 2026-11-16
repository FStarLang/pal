#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* The result may be NULL, and nothing says it is not. */

struct inner { uint32_t a; uint32_t b; };
struct ctx { struct inner in; uint32_t has; };
struct req { struct ctx *c; uint32_t k; };

struct inner *get_lead(struct req *r)
    _ensures(return == NULL || return == &r->c->in);

void unchecked(struct req *r)
{
    struct inner *q = get_lead(r);
    q->a = 1;
}
