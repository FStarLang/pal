#include "pal.h"
#include <stdint.h>

// A union member with no byte-level representation (a flexible-array
// struct) is left out of the union's model; the union, and the records
// embedding it, still translate, as does code using its other members.
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

typedef struct owner {
  uint64_t size;
  ctx rebuild;
} owner;

void take_ctx(ctx *c);

uint64_t get_size(owner *o) { return o->size; }

void pass(owner *o) { take_ctx(&o->rebuild); }

uint32_t get_n(ctx *c) { return c->n; }
