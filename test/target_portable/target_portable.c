#include "pal.h"
#include <stdint.h>

/* Translated with `--portable`, so nothing is assumed about the byte order:
 * only facts that hold on every target verify. A word whose bytes are all
 * equal reads back the same whichever end comes first. */

union word {
  uint32_t w;
  uint8_t b[4];
};

uint8_t any_byte(void)
  _ensures(return == 0x5a)
{
  union word u;
  u.w = 0x5a5a5a5au;
  return u.b[2];
}

uint8_t zero_byte(void)
  _ensures(return == 0)
{
  union word u;
  u.w = 0;
  return u.b[1];
}
