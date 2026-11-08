#include "pal.h"
#include <stdint.h>

// A struct whose `_refine` calls a `_pure` C function is not yet a
// proposition PAL can state of every element of an `_array`, so the array
// parameter is refused rather than given a weaker contract.

_pure _Bool small_ok(uint32_t v) { return v < 100; }

struct _refine(small_ok(this.v)) small {
  uint32_t v;
};

uint32_t read_small(_array struct small *a)
  _requires(a._length == 1)
{
  return a[0].v;
}
