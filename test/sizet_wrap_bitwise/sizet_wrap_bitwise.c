#include "pal.h"
#include <stddef.h>

#define ONES ((size_t)-1 / 255)
#define HIGHS (ONES * (255 / 2 + 1))
#define HASZERO(x) (((x) - ONES) & ~(x) & HIGHS)

/* musl's word-at-a-time zero-byte test: wrapping `-`, `~` and `&`. */
size_t has_zero(size_t x) { return HASZERO(x); }

/* Unsigned arithmetic wraps rather than owing anything... */
size_t wrap_add(void) _ensures(return == 0) {
  size_t m = (size_t)-1;
  return m + 1;
}

size_t wrap_sub(size_t z) _requires(z == 0) _ensures(return > z) { return z - 1; }

/* ...and is exact when it does not wrap. */
size_t dec(size_t x) _requires(x > 0) _ensures(return == x - 1) { return x - 1; }

/* The width is abstract, so the bitwise results are known by their bounds. */
size_t mask(size_t a, size_t b) _ensures(return <= a && return <= b) { return a & b; }

size_t set(size_t a, size_t b) _ensures(return >= a && return >= b) { return a | b; }

size_t flip(size_t a, size_t b) { return ~(a ^ b); }

size_t shifts(void) _ensures(return == 2) {
  size_t a = 1;
  return (a << 3) >> 2;
}

size_t shift_by(size_t a, unsigned s) _requires(s < 32) { return a >> s; }

size_t div3(size_t x) _ensures(return == x / 3) { return x / 3; }
