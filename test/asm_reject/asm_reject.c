#include "pal.h"
#include <stdint.h>

// Only an empty template without outputs or labels is a no-op.
void nonempty(void) { __asm__ __volatile__ ("nop"); }

int output(int x) {
  __asm__ ("" : "=r"(x));
  return x;
}
