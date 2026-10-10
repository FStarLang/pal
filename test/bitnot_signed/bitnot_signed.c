#include "pal.h"
#include <stdint.h>

// `~` of a signed operand: the kernel's `flags &= ~SOME_FLAG`, where the
// macro is an `int` constant (issue #349).
#define FLAG_X 0x10

struct dev { uint32_t flags; int16_t mode; };

void clear_x(struct dev *d)
  _preserves(_live(*d))
{
  d->flags &= ~FLAG_X;
  d->mode = ~d->mode;
}

int32_t complement(int32_t x)
{
  return ~x;
}

int8_t complement8(int8_t x)
{
  return ~x;
}
