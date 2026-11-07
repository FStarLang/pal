#include "pal.h"
#include <stdint.h>

/* A loop whose body cannot finish says nothing about the code after the
   loop: the condition is false on entry here, and the assertion after the
   loop is false, so this must not verify. */
void after_diverging_loop(uint32_t n)
  _requires(n <= 5u)
{
  while (n > 5u)
    _invariant(n <= 5u)
  {
    _assert(0);
  }
  _assert(n == 100u);
}
