#include "pal.h"
#include <stdint.h>

/* Translated for a big-endian target (`compile_flags.txt` selects MIPS), so the
 * first byte of a word is its most significant one. The same proof fails on a
 * little-endian target, where that byte is the least significant one. */

union word {
  uint32_t w;
  uint8_t b[4];
};

uint8_t first_byte(void)
  _ensures(return == 0x12)
{
  union word u;
  u.w = 0x12345678u;
  return u.b[0];
}

uint8_t last_byte(uint32_t x)
  _ensures(return == _old(x) % 256)
{
  union word u;
  u.w = x;
  return u.b[3];
}
