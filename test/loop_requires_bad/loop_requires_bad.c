// A loop's `_requires` has to hold again at the end of every iteration that
// does not `break`.
#include "pal.h"
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

void batch_overrun(uint32_t *done, uint32_t n)
  _requires(*done == 0)
{
  uint32_t k = 0;
  while (k < n)
    _invariant(_live(k) && k <= n)
    _requires(*done <= 8)
  {
    if (*done < 1000) {
      *done = *done + 1;
    }
    k++;
  }
}
