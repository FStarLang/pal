#include "pal.h"
#include <stddef.h>
#include <stdint.h>
typedef uint64_t word;
/* `wd - w0` counts words, but a position in `d` counts bytes: both are
   rejected rather than read as byte counts. */
void f(_array unsigned char *d)
  _requires(d._length >= 16 && d._length <= PTRDIFF_MAX && (uintptr_t)d % 8 == 0)
{
  word *wd = (void *)d;
  word *w0 = wd;
  wd++;
  _assert(wd - w0 == 8);
}
void g(_array unsigned char *d, size_t n)
  _requires(d._length == 16 && n == 2 && (uintptr_t)d % 8 == 0)
{
  word *wd = (void *)d;
  word *w0 = wd;
  for (; n; n--, wd++)
    _invariant(wd - w0 == 8 * (_specint)(2 - n) && n <= 2 && (uintptr_t)wd % 8 == 0)
  { *wd = 0; }
}
