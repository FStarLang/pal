#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* Non-null only when the field was set: the getter returns NULL otherwise. */

struct inner {
    uint32_t a;
};

struct ctx {
    uint32_t has;
    struct inner in;
};

struct req {
    struct ctx *c;
    uint32_t k;
};

struct inner *get_lead(struct req *r)
    _ensures(return == NULL || return == &r->c->in)
    _ensures(return != NULL)
{
    struct inner *q = NULL;
    if (r->c->has != 0)
    {
        q = &r->c->in;
    }
    return q;
}
