#include "pal.h"
#include <stddef.h>
#include <stdint.h>

size_t bytes_len(_array const unsigned char *s)
  _requires(_exists(size_t i, i < s._length && s[i] == 0))
  _ensures(return < s._length && s[return] == 0);

/* A suffix lent to an array parameter must have the parameter's element type:
   its bytes are not an array of wchar_t elements. */
size_t tail_bytes(_array const wchar_t *s, size_t i)
  _requires(i < s._length && _exists(size_t j, j < s._length && s[j] == 0))
{
  return bytes_len((const unsigned char *)(s + i));
}
