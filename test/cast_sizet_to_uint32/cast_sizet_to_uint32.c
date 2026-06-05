#include "pal.h"
#include <stddef.h>
#include <stdint.h>

uint32_t sizet_to_u32(size_t n)
  _requires((_specint) n <= UINT32_MAX)
  _ensures((_specint) return == n)
{
  return (uint32_t) n;
}

int32_t sizet_to_i32(size_t n)
  _requires((_specint) n <= INT32_MAX)
  _ensures((_specint) return == n)
{
  return (int32_t) n;
}
