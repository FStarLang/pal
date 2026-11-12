#include "pal.h"
#include <stdint.h>
#include <stddef.h>

// Field addresses of an object reached through a local pointer variable that
// a ghost statement hands the object to, as a library lemma does for a pointer
// a call returned.

struct stats { uint64_t packets; uint64_t bytes; };

void swap(uint64_t *a, uint64_t *b)
  _requires(_live(*a) && _live(*b))
  _ensures(*a == _old(*b) && *b == _old(*a))
{ uint64_t t = *a; *a = *b; *b = t; }

void bump(uint64_t *a)
  _requires(_live(*a) && *a < 100)
  _ensures(*a == _old(*a) + 1)
{ *a = *a + 1; }

void swap_local(struct stats *s)
  _requires(_live(*s))
  _ensures(s->packets == _old(s->bytes) && s->bytes == _old(s->packets))
{
  struct stats *p = NULL;
  p = s;
  _ghost_stmt(rewrite each $(s) as $(p));
  swap(&p->packets, &p->bytes);
  _ghost_stmt(rewrite each $(p) as $(s));
}

void bump_local(struct stats *s)
  _requires(_live(*s) && s->packets < 100)
  _ensures(s->packets == _old(s->packets) + 1 && s->bytes == _old(s->bytes))
{
  struct stats *p = NULL;
  p = s;
  _ghost_stmt(rewrite each $(s) as $(p));
  bump(&p->packets);
  _ghost_stmt(rewrite each $(p) as $(s));
}
