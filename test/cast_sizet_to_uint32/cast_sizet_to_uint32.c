#include "pal.h"
#include <stddef.h>
#include <stdint.h>

uint32_t sizet_to_u32(size_t n)
  _requires((_specint) n <= UINT32_MAX)
{
  return (uint32_t) n;
}
