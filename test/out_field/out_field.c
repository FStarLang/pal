#include "pal.h"
#include <stdint.h>

// Fields of an owned struct passed as `_out` arguments (issue #348).

struct stats { uint64_t packets; uint64_t bytes; };

void read2(_out uint64_t *p, _out uint64_t *b)
  _ensures(*p == 1 && *b == 2)
{ *p = 1; *b = 2; }

void read1(_out uint64_t *p)
  _ensures(*p == 1)
{ *p = 1; }

void get_one(struct stats *s)
  _requires(_live(*s))
  _ensures(s->packets == 1 && s->bytes == _old(s->bytes))
{
  read1(&s->packets);
}

void get_stats(struct stats *s)
  _requires(_live(*s))
  _ensures(s->packets == 1 && s->bytes == 2)
{
  read2(&s->packets, &s->bytes);
}

// The same split for parameters that borrow a field rather than fill it.

void bump(uint64_t *a)
  _requires(_live(*a) && *a < 100)
  _ensures(*a == _old(*a) + 1)
{ *a = *a + 1; }

void bump_field(struct stats *s)
  _requires(_live(*s) && s->packets < 100)
  _ensures(s->packets == _old(s->packets) + 1 && s->bytes == _old(s->bytes))
{
  bump(&s->packets);
}

void swap(uint64_t *a, uint64_t *b)
  _requires(_live(*a) && _live(*b))
  _ensures(*a == _old(*b) && *b == _old(*a))
{ uint64_t t = *a; *a = *b; *b = t; }

void swap_fields(struct stats *s)
  _requires(_live(*s))
  _ensures(s->packets == _old(s->bytes) && s->bytes == _old(s->packets))
{
  swap(&s->packets, &s->bytes);
}

// A struct field of a struct, and a local filled by the call.
struct wrap { uint32_t tag; struct stats st; };

void get_nested(struct wrap *w)
  _requires(_live(*w))
  _ensures(w->st.packets == 1 && w->st.bytes == 2 && w->tag == _old(w->tag))
{
  read2(&w->st.packets, &w->st.bytes);
}

uint64_t get_local(void)
  _ensures(return == 3)
{
  struct stats st;
  read2(&st.packets, &st.bytes);
  return st.packets + st.bytes;
}
