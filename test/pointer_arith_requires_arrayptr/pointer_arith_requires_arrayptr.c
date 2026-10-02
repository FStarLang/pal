#include "pal.h"
#include <stdint.h>

typedef struct Cell {
  uint32_t x;
} Cell;

typedef struct Holder {
  Cell *p;
} Holder;

void advance_plain_field(Holder *h)
{
  h->p++;
}
