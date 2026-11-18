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

/* Changing the tag alone breaks the `_refine` of what the struct owns. */
void retag(struct req *r)
{
    r->c->hdr.lead.k = kind_b;
}
