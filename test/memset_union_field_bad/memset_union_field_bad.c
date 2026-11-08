// All-zero bytes would represent either member, but `memset` makes only the
// first named member live; claiming the second is not provable.
#include "pal.h"
#include <stddef.h>
#include <stdint.h>
#include <string.h>

typedef struct {
  union {
    uint64_t header_crc;
    uint64_t body_crc;
  } calc;
  uint32_t count;
} parse_state;

void reset_wrong_arm(parse_state *s)
  _ensures(s->calc.body_crc._active)
{
  memset(s, 0, sizeof(*s));
}
