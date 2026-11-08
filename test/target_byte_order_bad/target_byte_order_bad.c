#include "pal.h"
#include <stdint.h>

/* Translated for the host, which is little-endian: the first byte of a word is
 * its least significant one, so the big-endian claim must not verify. (The
 * same function verifies in `target_big_endian`, translated for MIPS.) */

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
