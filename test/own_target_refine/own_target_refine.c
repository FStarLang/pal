#include "pal.h"
#include <stdint.h>

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

struct hdr { uint64_t seq; unit_id lead; };

struct ctx {
    uint32_t flags;
    struct hdr hdr;
};

struct req {
    uint32_t id;
    struct ctx *c;
};

/* What a struct owns through a pointer satisfies its type's `_refine`, and
   those of the structs embedded in it, so a reader that checks the tag may
   read the member it names. */

uint32_t lead_eu(struct req *r)
    _requires(r->c->hdr.lead.k == kind_b)
{
    return r->c->hdr.lead.b.eu;
}

unit_id lead(struct req *r)
{
    unit_id u = r->c->hdr.lead;
    return u;
}

/* A write that keeps the tag and its member in step is allowed. */
void set_b(struct req *r, uint32_t eu)
{
    unit_id u = {.k = kind_b, .b = {.eu = eu}};
    r->c->hdr.lead = u;
}
