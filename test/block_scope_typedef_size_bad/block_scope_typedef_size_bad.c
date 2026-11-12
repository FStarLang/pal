#include "pal.h"
#include <stddef.h>
#include <stdint.h>

// The local `size_t` is `uint8_t`, so 255 + 1 wraps to 0.
uint32_t shadow_size(void)
  _ensures(return == 256)
{
  typedef uint8_t size_t;
  size_t x = 255;
  x = x + 1;
  return x;
}
