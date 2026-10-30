#include "pal.h"
#include <stdint.h>

struct owner;

struct owner_member {
  struct owner *parent;
  uint32_t value;
};

struct owner {
  struct owner_member member;
};

uint32_t read_unowned_parent(const struct owner_member *p)
  _requires(_inline_pulse(emp))
{
  return p->parent->member.value;
}
