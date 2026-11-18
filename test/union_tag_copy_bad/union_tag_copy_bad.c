#include "pal.h"
#include <stdbool.h>
#include <stdint.h>

/* The `_refine` says which member is live only when the tag is `kind_b`. For
   any other tag the copy reads the first member, and nothing says it is
   live, so the copy must not verify. */

typedef enum { kind_unset = 0, kind_a = 1, kind_b = 2 } kind;

struct a_id { int64_t drive; uint32_t n; };
struct b_id { uint32_t eu; uint32_t lane; uint64_t gen; };

typedef struct _refine(this.k != kind_b || this.b._active) unit_id
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
