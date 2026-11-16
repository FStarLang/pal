#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

/* A union arm holding a flexible-array struct, padded out by a byte array
   arm, is lent to callees that take the flexible struct itself. The arm is
   lent as that struct, with the tail the padding gives it, and taken back
   with the same length; a callee that may store through it changes the
   arm, and nothing else. */

struct bitmap {
    uint64_t count;
    uint64_t bits[];
};

bool check(const struct bitmap *b, uint64_t i);

void set(struct bitmap *b, uint64_t i);

struct ctx {
    uint32_t k;
    union {
        struct bitmap bm;
        uint8_t storage[32];
    };
};

struct req {
    struct ctx *c;
    uint32_t n;
};

bool probe(struct ctx *c, uint64_t i)
    _requires(c->bm._active)
    _ensures(c->bm._active)
    _ensures(c->k == _old(c->k))
{
    return check(&c->bm, i);
}

bool update(struct ctx *c, uint64_t i)
    _requires(c->bm._active)
    _ensures(c->bm._active)
    _ensures(c->k == _old(c->k))
{
    set(&c->bm, i);
    set(&c->bm, i + 1);
    return check(&c->bm, i);
}

bool deep(struct req *r, uint64_t i)
    _requires(r->c->bm._active)
    _ensures(r->c->bm._active)
{
    set(&r->c->bm, i);
    return check(&r->c->bm, i);
}

struct bitmap *get_bm(struct req *r)
    _ensures(return == &r->c->bm)
    _ensures(r->c == _old(r->c))
    _ensures(_unchanged(*r->c))
{
    return &r->c->bm;
}

bool aliased(struct req *r, uint64_t i)
    _requires(r->c->bm._active)
    _ensures(r->c->bm._active)
{
    struct bitmap *b = &r->c->bm;
    set(b, i);
    return check(b, i);
}

bool got(struct req *r, uint64_t i)
    _requires(r->c->bm._active)
    _ensures(r->c->bm._active)
{
    struct bitmap *b = get_bm(r);
    set(b, i);
    return check(b, i);
}
