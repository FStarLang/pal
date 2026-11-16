#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* A getter that returns the address of a field, or NULL when there is none. */

struct inner { uint32_t a; uint32_t b; };
struct ctx { struct inner in; uint32_t has; };
struct req { struct ctx *c; uint32_t k; };

struct inner *get_lead(struct req *r)
    _ensures(return == NULL || return == &r->c->in)
    _ensures(r->c->has == _old(r->c->has))
    _ensures(r->c->has != 0 ==> return != NULL);

/* Checked by the caller. */
uint32_t checked(struct req *r)
{
    struct inner *q = NULL;
    r->k = 0;
    q = get_lead(r);
    if (q == NULL)
    {
        return 0;
    }
    q->a = 1;
    _assert(r->c->in.a == 1);
    return q->a + 1;
}

/* Known non-NULL from the getter's contract. */
void known(struct req *r)
    _requires(r->c->has != 0)
{
    struct inner *q = get_lead(r);
    _assert(q != NULL);
    q->b = 7;
    _assert(r->c->in.b == 7);
}

/* `!q` and a plain truth test are tests too. */
uint32_t truthy(struct req *r)
{
    struct inner *q = get_lead(r);
    if (!q)
    {
        return 0;
    }
    if (q)
    {
        q->a = 2;
    }
    return 1;
}
