#include "pal.h"
#include <stdint.h>
#include <stddef.h>

struct inner { uint32_t a; uint32_t b; };
struct ctx { struct inner in; uint32_t n; };

struct inner *get_in(struct ctx *o)
    _ensures(return == &o->in)
{
    return &o->in;
}

void bump(struct inner *p);

/* Declared `_plain`, `q` is a pointer object rather than an alias of `o->in`:
   its uses read the local, so a ghost may lend `o->in` out of `*o` and pass
   it on through `q`. As an alias, `q->a` would be `o->in.a`, which focuses
   `*o` -- ownership the ghost has taken apart. */
void plain_local(struct ctx *o)
{
    _plain struct inner *q = get_in(o);
    _ghost_stmt(struct_ctx_focus_in $(o);
                rewrite each ($(o) +! struct_ctx_offsetof_in) as $(q));
    bump(q);
    q->a = 1;
    _ghost_stmt(rewrite each $(q) as ($(o) +! struct_ctx_offsetof_in);
                struct_ctx_unfocus_in $(o));
}

/* Without `_plain`, the same local is an alias, and each use of it is
   `o->in` itself. */
void alias_local(struct ctx *o)
{
    struct inner *q = get_in(o);
    q->a = 1;
    _assert(o->in.a == 1);
}
