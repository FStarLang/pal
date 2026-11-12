#include "pal.h"
#include <stdint.h>

// Using a union member that has no byte-level representation is rejected
// at the use.
typedef struct bitmap {
  uint64_t count;
  uint64_t data[];
} bitmap;

typedef struct ctx {
  uint32_t n;
  union {
    bitmap bits;
    uint8_t storage[sizeof(bitmap) + 4 * sizeof(uint64_t)];
  };
} ctx;

uint64_t bits_count(ctx *c) { return c->bits.count; }

uint32_t get_n(ctx *c) _requires(c->bits.count == 0) { return c->n; }
