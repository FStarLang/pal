#include "pal.h"
#include <stdint.h>

/* As call_nested_arm_lend, but get says nothing about what it returns, so
   finish cannot show the status is unchanged. */

struct base {
    uint32_t status;
    uint32_t other;
};

union outer {
    struct base b;
    uint8_t pad[16];
};

struct pair {
    uint32_t lo;
    uint32_t hi;
};

struct pair get(const struct base *b);

void put(struct base *b, struct pair s)
    _ensures(b->status == s.lo)
    _ensures(b->other == _old(b->other));

void finish(union outer *o)
    _requires(o->b._active)
    _ensures(o->b._active)
    _ensures(o->b.status == _old(o->b.status))
{
    put(&o->b, get(&o->b));
}
