#include "pal.h"
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

// Issue #353: a packed header whose fields happen to sit at offsets their
// types' alignments divide. The struct itself is only 1-aligned, so `len`
// is accessed as unaligned all the same.
struct __attribute__((packed)) hdr {
  uint8_t status;
  uint8_t pad;
  uint16_t len;
};

// Fields that really are misaligned: `b` at offset 1, `c` at offset 5.
struct __attribute__((packed)) mis {
  uint8_t a;
  uint32_t b;
  uint16_t c;
};

// A misaligned pointer field.
struct __attribute__((packed)) pm {
  uint8_t tag;
  uint16_t *p;
};

// A packed struct nested in another: 1-aligned, so aligned anywhere, and
// its own misaligned field is reached through it.
struct __attribute__((packed)) outer {
  uint8_t x;
  struct mis m;
};

// Packing that only lowers the struct's alignment: `b` is at offset 4, which
// 4 divides, but the struct is 2-aligned, so `b` is not.
#pragma pack(push, 2)
struct p2 {
  uint16_t a;
  uint16_t pad;
  uint32_t b;
};
#pragma pack(pop)

uint16_t get_len(struct hdr *h)
  _ensures(return == h->len)
{
  return h->len;
}

void set_len(struct hdr *h, uint16_t n)
  _ensures(h->len == n)
  _ensures(h->status == _old(h->status))
{
  h->len = n;
}

uint32_t get_b(struct mis *m)
  _ensures(return == m->b)
{
  return m->b;
}

void set_bc(struct mis *m, uint32_t v, uint16_t w)
  _ensures(m->b == v)
  _ensures(m->c == w)
  _ensures(m->a == _old(m->a))
{
  m->b = v;
  m->c = w;
}

void bump_b(struct mis *m)
  _requires(m->b < 100)
  _ensures(m->b == _old(m->b) + 1)
{
  m->b = m->b + 1;
}

uint32_t local(void)
  _ensures(return == 7)
{
  struct mis m = { 1, 7, 9 };
  m.c = 3;
  return m.b;
}

struct mis copy(struct mis *m)
  _ensures(return.b == m->b)
{
  return *m;
}

void store(struct mis *m, struct mis v)
  _ensures(m->b == v.b)
{
  *m = v;
}

_Bool has_p(struct pm *m)
{
  return m->p != NULL;
}

uint32_t outer_b(struct outer *o)
  _ensures(return == o->m.b)
{
  return o->m.b;
}

void set_outer_b(struct outer *o, uint32_t v)
  _ensures(o->m.b == v)
  _ensures(o->x == _old(o->x))
{
  o->m.b = v;
}

uint32_t p2_b(struct p2 *s)
  _ensures(return == s->b)
{
  return s->b;
}

uint32_t elem_b(_array struct mis *ms, size_t i)
  _requires(i < ms._length)
  _preserves_value(ms._length)
  _ensures(return == ms[i].b)
{
  return ms[i].b;
}

void set_elem_c(_array struct mis *ms, size_t i, uint16_t w)
  _requires(i < ms._length)
  _preserves_value(ms._length)
  _ensures(ms[i].c == w)
{
  ms[i].c = w;
}

uint32_t local_fields(void)
  _ensures(return == 5)
{
  struct mis m;
  m.a = 1;
  m.b = 5;
  m.c = 2;
  return m.b;
}

void partial(void)
{
  struct mis m;
  m.b = 5;
  m.a = (uint8_t)m.b;
}

uint32_t heap_mis(void)
{
  struct mis *m = malloc(sizeof(struct mis));
  if (!m) return 0;
  m->a = 1;
  m->b = 5;
  m->c = 2;
  uint32_t r = m->b;
  free(m);
  return r;
}
