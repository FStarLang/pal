#include "pal.h"
#include <stdint.h>

uint32_t read_without_ownership(_plain _array const uint32_t *a, uint32_t i)
  _requires(i == 0)
{
  return a[i];
}
