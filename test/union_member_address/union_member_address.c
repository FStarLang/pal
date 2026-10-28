#include "pal.h"
#include <stdint.h>

struct pair {
    uint32_t first;
    uint32_t last;
};

union choice {
    uint32_t scalar;
    struct pair pair;
};

struct holder {
    uint64_t prefix;
    union choice value;
};

uint32_t read_value(const uint32_t *p)
    _ensures(return == *p)
{
    return *p;
}

void write_value(uint32_t *p, uint32_t value)
    _ensures(*p == value)
{
    *p = value;
}

uint32_t read_pair(const struct pair *p)
    _ensures(return == p->last)
{
    return p->last;
}

_Bool same_address(const union choice *u)
    _ensures(return)
    _ensures(&u->scalar == &u->pair.first)
{
    _ghost_stmt(assert pure ($(&u->scalar) == $(&u->pair.first)));
    return &u->scalar == &u->pair.first;
}

uint32_t read_member_field(union choice *u)
    _requires(u->pair._active)
    _ensures(return == u->pair.last)
{
    return read_value(&u->pair.last);
}

uint32_t read_whole_member(union choice *u)
    _requires(u->pair._active)
    _ensures(return == u->pair.last)
{
    return read_pair(&u->pair);
}

void write_member_field(union choice *u, uint32_t value)
    _requires(u->pair._active)
    _ensures(u->pair._active)
    _ensures(u->pair.last == value)
    _ensures(u->pair.first == _old(u->pair.first))
{
    write_value(&u->pair.last, value);
}

uint32_t read_nested_member(struct holder *h)
    _requires(h->value.pair._active)
    _ensures(return == h->value.pair.last)
{
    return read_value(&h->value.pair.last);
}
