// An `_out` struct filled one field at a time, where a field already written
// is written again before the struct is complete: straight-line, and in an
// `if`. The second write is to an initialized field and must not be treated
// as the first.

#include "pal.h"
#include <stdint.h>

typedef enum { K_UNSET = 0, K_A = 1, K_B = 2 } KIND;

struct params { uint32_t a; uint32_t kind; uint32_t b; };

void params_init(_out struct params *p, uint32_t a, uint32_t kind, uint32_t b)
{
    p->a = a;
    p->kind = kind;
    p->kind = 2;
    p->b = b;
}

struct id { uint64_t x; uint64_t y; };

void id_init(_out struct id *i, uint64_t x) { i->x = x; i->y = 0; }

struct kparams { struct id id; uint32_t a; KIND kind; _Bool b; };

void kparams_init(_out struct kparams *p, uint32_t a, KIND kind, uint64_t v, _Bool b)
{
    id_init(&p->id, v);
    p->a = a;
    p->kind = kind;
    if (kind == K_UNSET && v != 0)
    {
        p->kind = K_B;
    }
    p->b = b;
}
