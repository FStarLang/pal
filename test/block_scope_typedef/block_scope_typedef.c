#include "pal.h"
#include <stddef.h>
#include <stdint.h>

// A block-scope typedef is a local spelling of its underlying type.
// Two functions may each declare their own `word`, at different types.
uint32_t widen(uint16_t x)
  _ensures(return == x)
{
  typedef uint32_t word;
  typedef word word2;
  word2 w = x;
  return w;
}

uint8_t narrow(uint8_t x)
  _ensures(return == x)
{
  typedef uint8_t word;
  word w = x;
  return w;
}

size_t count(size_t n)
  _ensures(return == n)
{
  typedef size_t sz;
  sz r = n;
  return r;
}

// musl's word-at-a-time idiom: a `__may_alias__` typedef to read through.
uint32_t read_word(const uint32_t *p)
  _ensures(return == *p)
{
  typedef uint32_t __attribute__((__may_alias__)) u32;
  return *(const u32 *)p;
}

// A local `size_t` is the program's own type, not the target's.
uint32_t shadow_size(void)
  _ensures(return == 0)
{
  typedef uint8_t size_t;
  size_t x = 255;
  x = x + 1;
  return x;
}
