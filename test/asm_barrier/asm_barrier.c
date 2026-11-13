#include "pal.h"
#include <stddef.h>
#include <stdint.h>

// musl's explicit_bzero: an empty asm with only inputs is a compiler barrier
// and translates as a no-op, after evaluating its inputs.
void zero(_array uint8_t *d, size_t n)
  _requires(n <= d._length)
  _ensures(d._length == _old(d._length))
  _ensures(_forall(size_t k, k < n ==> d[k] == 0))
{
  for (size_t i = 0; i < n; i++)
    _invariant(i <= n && d._length == _old(d._length))
    _invariant(_forall(size_t k, k < i ==> d[k] == 0))
  {
    d[i] = 0;
  }
  __asm__ __volatile__ ("" : : "r"(d) : "memory");
}

int count(int x)
  _requires(x < 100)
  _ensures(return == x + 1)
{
  __asm__ __volatile__ ("" : : "r"(x++) : "memory");
  __asm__ ("");
  return x;
}
