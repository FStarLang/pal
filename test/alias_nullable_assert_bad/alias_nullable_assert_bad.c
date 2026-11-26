#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* `q` may be NULL, so `_assert(q->a == 1)` is not a statement about
   `r->c->in`: it is guarded by `q != NULL` like any other use of `q`, and
   nothing says the getter did not return NULL. */

struct inner { uint32_t a; uint32_t b; };
struct ctx { struct inner in; uint32_t has; };
struct req { struct ctx *c; uint32_t k; };

struct inner *get_lead(struct req *r)
    _ensures(r->c == _old(r->c))
    _ensures(return == NULL || return == &r->c->in);

void f(struct req *r)
{
    struct inner *q = get_lead(r);
    r->c->in.a = 1;
    _assert(q->a == 1);
}
