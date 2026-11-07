// `memset` of a struct with a union field: the union is zeroed through its
// first named member, as for implicit initialization.
#include "pal.h"
#include <stddef.h>
#include <stdint.h>
#include <string.h>

typedef struct {
  uint64_t crc;
} crc64;

typedef struct {
  union {
    crc64 header_crc;
    crc64 body_crc;
  } calc;
  uint32_t count;
  uint8_t full : 1;
  uint8_t kind : 3;
  uint8_t unused[3];
  uint8_t state;
} parse_state;

typedef struct {
  uint32_t status;
  union {
    uint8_t opaque[32];
    parse_state parse;
  } u;
} parser;

void reset(parse_state *s)
  _ensures(s->count == 0 && s->state == 0 && s->full == 0)
  _ensures(s->calc.header_crc._active && s->calc.header_crc.crc == 0)
{
  memset(s, 0, sizeof(*s));
}

void reset_arm(parser *p)
  _requires(p->u.parse._active)
  _ensures(p->u.parse._active && p->u.parse.count == 0)
  _ensures(p->status == _old(p->status))
{
  memset(&p->u.parse, 0, sizeof(p->u.parse));
}
