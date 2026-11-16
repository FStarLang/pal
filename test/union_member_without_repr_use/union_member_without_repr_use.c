#include "pal.h"
#include <stdint.h>

// A nested flexible struct still has no byte-level representation. Unlike
// a direct flexible union member, it cannot get a sized union-arm view.
typedef struct bitmap {
  uint64_t count;
  struct { uint64_t size; uint64_t data[]; } tail;
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
