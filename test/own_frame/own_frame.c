#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

/* A conditional with an `_ensures`, and a loop, both rebind the value of a
   parameter whose struct owns a pointer. What the pointer reaches is owned
   at that value, so it is rebound along with it, and a clause can reach
   through the pointer to say what is still true there. */

struct ctx {
    bool has;
    uint32_t v;
};

struct req {
    struct ctx *c;
    uint32_t n;
};

uint32_t get_v(struct req *r)
    _requires(r->c->has)
    _ensures(r->c == _old(r->c))
    _ensures(r->c->has)
    _ensures(return == r->c->v);

void bump(struct req *r)
    _ensures(r->c == _old(r->c))
    _ensures(r->c->has == _old(r->c->has));

uint32_t pick(struct req *r, bool f)
    _requires(r->c->has)
    _ensures(r->c->has)
{
    uint32_t x = 0;
    if (f)
        _ensures(r->c->has)
    {
        x = get_v(r);
    }
    else
    {
        r->n = 1;
    }
    x = get_v(r);
    return x;
}

uint32_t loop(struct req *r, uint32_t k)
    _requires(r->c->has)
    _ensures(r->c->has)
{
    uint32_t i = 0;
    uint32_t x = 0;
    while (i < k)
        _invariant(_live(i) && _live(k))
        _invariant(r->c->has)
    {
        bump(r);
        i = i + 1;
    }
    x = get_v(r);
    return x;
}

/* The stronger Pulse join retains a fact established by both arms even
   when the annotation only names a live local. */
uint32_t inferred_pick(struct req *r, bool f)
    _requires(r->c->has)
{
    uint32_t x = 0;
    if (f)
        _ensures(_live(x))
    {
        x = get_v(r);
    }
    return get_v(r);
}
