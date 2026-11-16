#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

/* A struct whose `_refine` ties the live member of its union to a tag field
   is copied whole. The copy reads the tag first and the member it names
   after, so it needs only what the `_refine` already says -- including for
   the tags it leaves to the remaining member. */

typedef enum { kind_unset = 0, kind_a = 1, kind_b = 2 } kind;

struct a_id { int64_t drive; uint32_t n; };
struct b_id { uint32_t eu; uint32_t lane; uint64_t gen; };

typedef struct _refine(
    (this.k != kind_b || this.b._active) &&
    (this.k == kind_b || this.a._active)) unit_id
{
    kind k;
    union {
        struct a_id a;
        struct b_id b;
    };
} unit_id;

struct ctx {
    uint32_t flags;
    unit_id lead;
};

unit_id get_lead(const struct ctx *c)
{
    unit_id u = c->lead;
    return u;
}

void set_lead(struct ctx *c, unit_id u)
{
    c->lead = u;
}

unit_id make_b(uint32_t eu)
{
    unit_id u = {.k = kind_b, .b = {.eu = eu}};
    return u;
}

unit_id get_lead_kind(const struct ctx *c)
    _ensures(return.k == c->lead.k)
{
    unit_id u = c->lead;
    return u;
}

/* The returned copy carries the `_refine`, so a caller that checks its tag
   may read the member the tag names. */
uint32_t lead_eu(const struct ctx *c)
    _requires(c->lead.k == kind_b)
{
    unit_id u = get_lead_kind(c);
    return u.b.eu;
}

uint32_t made_eu(uint32_t eu)
{
    unit_id u = make_b(eu);
    if (u.k == kind_b)
        return u.b.eu;
    return 0;
}
