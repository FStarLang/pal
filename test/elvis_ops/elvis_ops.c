#include "pal.h"
#include <stdint.h>

/* GNU `a ?: b` yields `a` when it is nonzero and `b` otherwise, evaluating
 * `a` only once. PAL desugars it to `a ? a : b`, which is only faithful when
 * `a` has no side effects.
 * An effectful left operand is reported as unsupported. */

int32_t elvis_ops_int(int32_t a, int32_t b)
    _ensures(return == (a != 0 ? a : b)) {
  return a ?: b;
}

uint32_t elvis_ops_chain(uint32_t x, uint32_t y, uint32_t z)
    _ensures(return == (x != 0 ? x : (y != 0 ? y : z))) {
  return x ?: y ?: z;
}

int32_t elvis_ops_as_condition(int32_t flag, int32_t fallback)
    _ensures(return == ((flag != 0 ? flag : fallback) != 0 ? 1 : 0)) {
  if (flag ?: fallback) {
    return 1;
  }
  return 0;
}
