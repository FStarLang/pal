#include "pal.h"
#include <stdint.h>

/* A struct with an overlay union in it has no whole-value writer, so a
   compound literal stored into one is taken apart into a store per field,
   and the union's part into a store to the arm the literal initializes. */

union __attribute__((annotate("pal-overlay"))) u { uint32_t a; uint32_t b; };
struct t { uint8_t c; _Bool f; };
struct s { union u x; uint32_t n; struct t w; };
struct o { struct s in; uint32_t k; };

void zero(struct o *p)
{
    p->in = (struct s){0};
    _assert(p->in.n == 0);
    _assert(p->in.x.a == 0);
    _assert(p->in.w.c == 0);
}

void through_pointer(struct o *p)
{
    struct s *q = &p->in;
    *q = (struct s){ .x = { .b = 4 }, .n = 9 };
    _assert(p->in.n == 9);
    _assert(p->in.x.b == 4);
}
