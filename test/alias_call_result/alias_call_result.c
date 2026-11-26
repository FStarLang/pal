#include "pal.h"
#include <stdint.h>
#include <stddef.h>

struct inner { uint32_t a; uint32_t b; };
struct ctx { struct inner in; uint32_t n; };
struct req { struct ctx *c; uint32_t k; };

struct inner *get_in(struct ctx *o)
    _ensures(return == &o->in)
{
    return &o->in;
}

struct inner *get_deep(struct req *r)
    _ensures(return == &r->c->in)
{
    return &r->c->in;
}

void direct(struct ctx *o)
{
    struct inner *q = get_in(o);
    q->a = 1;
    q->b = q->a + 1;
    _assert(o->in.b == 2);
}

void deep(struct req *r)
{
    struct inner *q;
    q = get_deep(r);
    q->a = 3;
    _assert(r->c->in.a == 3);
}

/* C's usual shape: declared `NULL` at the top, bound by the call later. */
void late_bound(struct req *r)
{
    struct inner *q = NULL;
    r->k = 0;
    q = get_deep(r);
    q->b = 7;
    _assert(r->c->in.b == 7);
}

const struct inner *get_in_const(const struct ctx *o)
    _ensures(return == &o->in)
{
    return &o->in;
}

uint32_t through_const(struct ctx *o)
    _ensures(return == o->in.a)
{
    const struct inner *q = get_in_const(o);
    return q->a;
}

/* An alias handed to a callee lends it the field, as `&r->c->in` would. */
void set_a(struct inner *i, uint32_t v)
    _ensures(i->a == v)
    _ensures(i->b == _old(i->b));

void lend_deep(struct req *r)
{
    struct inner *q = get_deep(r);
    r->c->in.b = 4;
    set_a(q, 5);
    _assert(r->c->in.a == 5);
    _assert(r->c->in.b == 4);
}

uint32_t get_b(const struct inner *i)
    _ensures(return == i->b);

uint32_t lend_const(struct ctx *o)
    _ensures(return == o->in.b)
{
    const struct inner *q = get_in_const(o);
    return get_b(q);
}
