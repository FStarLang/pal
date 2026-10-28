#include "pal.h"
#include <stdint.h>

void unguarded_quotient(uint32_t n, uint32_t d)
{
  _assert(((_specint)n / d) * d <= n);
}
