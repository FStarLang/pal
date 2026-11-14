#include "pal.h"
#include <stddef.h>
#include <stdint.h>
typedef uint64_t word;

/* `w0 + 1` is a word on from `w0`, which is where `wd` is: not before it. */
void f(_array unsigned char *d)
  _requires(d._length >= 16 && d._length <= PTRDIFF_MAX && (uintptr_t)d % 8 == 0)
{
  word *wd = (void *)d;
  word *w0 = wd;
  wd++;
  _assert(w0 + 1 < wd);
}
