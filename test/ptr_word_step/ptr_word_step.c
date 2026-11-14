#include "pal.h"
#include <stddef.h>
#include <stdint.h>
typedef uint64_t word;

/* A word pointer walked over a byte array steps a word at a time: one
   past `w0` is where `wd` is after `wd++`, eight bytes on. */
void f(_array unsigned char *d)
  _requires(d._length >= 16 && d._length <= PTRDIFF_MAX && (uintptr_t)d % 8 == 0)
{
  word *wd = (void *)d;
  word *w0 = wd;
  wd++;
  _assert(w0 < wd && w0 + 1 <= wd && !(w0 + 1 < wd));
  _assert((unsigned char *)wd - d == 8);
}
