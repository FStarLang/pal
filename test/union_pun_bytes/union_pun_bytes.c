#include "pal.h"
#include <stdint.h>

/* Byte-level punning between union members: a scalar read or write through a
 * member that is not the live one is carried out on the bytes of the live
 * member, provided those bytes are all integer bytes. */

struct tag { uint16_t op; uint16_t flags; };
struct cmd { uint16_t op; uint16_t flags; uint32_t arg; };

union frame {
  struct cmd c;
  struct tag t;
  uint32_t half[2];
  uint8_t octet[8];
  uint64_t bits;
  int32_t shalf[2];
};

/* Common initial sequence. */
uint16_t frame_op(union frame *f)
  _requires(f->c._active)
  _ensures(f->c._active && return == f->c.op)
{
  return f->t.op;
}

void frame_set_flags(union frame *f, uint16_t v)
  _requires(f->c._active)
  _ensures(f->c._active && f->c.flags == v &&
           f->c.op == _old(f->c.op) && f->c.arg == _old(f->c.arg))
{
  f->t.flags = v;
}

/* A word covering two fields, and a byte inside a field. */
uint32_t frame_head(union frame *f)
  _requires(f->c._active)
  _ensures(f->c._active)
{
  return f->half[0];
}

uint8_t frame_arg_byte(union frame *f)
  _requires(f->c._active)
  _ensures(f->c._active)
{
  return f->octet[6];
}

/* A write into an array member's bytes leaves the other elements alone. */
void frame_set_op(union frame *f, uint16_t v)
  _requires(f->half._active)
  _ensures(f->half._active && f->half[1] == _old(f->half[1]))
{
  f->c.op = v;
}

/* Locally: the value written through one member is read back through another. */
uint32_t frame_roundtrip(uint32_t x)
  _ensures(return == x)
{
  union frame f;
  f.bits = 0;
  f.c.arg = x;
  return f.half[1];
}

int32_t frame_signed(uint32_t x)
{
  union frame f;
  f.bits = 0;
  f.half[0] = x;
  return f.shalf[0];
}
