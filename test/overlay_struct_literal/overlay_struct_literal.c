#include "pal.h"
#include <stdint.h>

/* A struct with an overlay union in it has no whole-value writer, so a
   compound literal stored into one is taken apart into a store per field,
   and the union's part into a store to the arm the literal initializes. */

struct pair { uint16_t lo; uint16_t hi; };
union __attribute__((annotate("pal-overlay"))) u { uint32_t a; uint32_t b; struct pair p; };
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

void arm_struct(struct o *p)
{
    p->in = (struct s){ .x = { .p = { .hi = 7 } } };
    _assert(p->in.x.p.hi == 7);
    _assert(p->in.x.p.lo == 0);
    _assert(p->in.n == 0);
}

struct fields { unsigned int tag : 7; unsigned int state : 25; };
union _overlay word { struct fields parts; uint32_t raw; };

uint32_t local_word(void)
{
    union word w = { .parts = { .state = 3 } };
    _assert(w.parts.tag == 0);
    _assert(w.parts.state == 3);
    return w.raw;
}

uint32_t replace_word(struct fields parts)
{
    union word w = {0};
    w.parts = parts;
    _assert(w.parts.tag == parts.tag);
    _assert(w.parts.state == parts.state);
    return w.raw;
}

union choice { struct s data; uint32_t other; };
struct tagged { union choice choice; uint32_t end; };

uint32_t replace_tagged(struct tagged *p)
{
    p->choice.other = 19;
    *p = (struct tagged){ .choice = { .data = { .x = { .b = 7 } } } };
    _assert(p->choice.data.n == 0);
    _assert(p->end == 0);
    return p->choice.data.x.b;
}

union _overlay payload { unsigned char bytes[16]; uint32_t words[4]; };
struct payload_field { union payload u; };

uint32_t clear_payload(struct payload_field *p)
{
    *p = (struct payload_field){0};
    _assert(p->u.bytes[15] == 0);
    return p->u.words[1];
}

union _overlay links { struct pair first; uint64_t wide; };
struct embedded_links { uint32_t id; union links links; unsigned char reserved[4]; };
struct fresh_links { struct embedded_links embedded; uint32_t end; };

uint32_t initialize_short_arm(_out struct fresh_links *p)
{
    *p = (struct fresh_links){ .embedded.links.first = { .hi = 7 } };
    _assert(p->embedded.links.first.lo == 0);
    _assert(p->embedded.reserved[3] == 0);
    _assert(p->end == 0);
    return p->embedded.links.first.hi;
}

void initialize_array_member(_out struct fresh_links *p)
{
    *p = (struct fresh_links){ .embedded = { .reserved = {1, 2, (unsigned char)259}, .id = 17 } };
    _assert(p->embedded.id == 17);
    _assert(p->embedded.reserved[2] == 3);
    _assert(p->embedded.reserved[3] == 0);
}
