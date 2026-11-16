#include "pal.h"
#include <stdint.h>

/* A struct returned whole promises its `_refine`: tag `kind_b` with the
   other member live is not one. */

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

unit_id bad_make(uint32_t n)
{
    unit_id u = {.k = kind_b, .a = {.n = n}};
    return u;
}
