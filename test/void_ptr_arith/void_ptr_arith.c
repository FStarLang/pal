#include "pal.h"
#include <stdint.h>

// GNU C: arithmetic on `void *` moves by bytes (sizeof(void) == 1).

void *advance(void *base) { return base + 4; }

void *back(void *base) {
  void *p = base + 4;
  return p - 2;
}

void *advance_compound(void *p) {
  p += 8;
  p++;
  return p;
}

// The MMIO idiom from the kernel: `readl(priv->base + OFFSET)`.
uint32_t readl(void *addr) _plain { return 0; }

uint32_t read_reg(void *base) { return readl(base + 0x10); }

long diff(void *a) {
  void *b = a + 12;
  return b - a;
}

// Dereferencing through a cast pointer reads at the cast-to type. A `void *`
// grants no ownership by its type, so the contract states it in Pulse.
_ghost_arg(uint32_t x)
_requires(_inline_pulse(uint32_t_pts_to $(base) 1.0R $(x)))
_ensures(_inline_pulse(uint32_t_pts_to $(base) 1.0R $(x)))
_ensures(return == x)
uint32_t read_cast(void *base) { return *(uint32_t *)base; }

_ghost_arg(uint32_t x)
_requires(_inline_pulse(uint32_t_pts_to $(base + 0x10) 1.0R $(x)))
_ensures(_inline_pulse(uint32_t_pts_to $(base + 0x10) 1.0R $(x)))
_ensures(return == x)
uint32_t read_at(void *base) { return *(uint32_t *)(base + 0x10); }

_ghost_arg(uint32_t x)
_requires(_inline_pulse(uint32_t_pts_to $(base + 8) 1.0R $(x)))
_ensures(_inline_pulse(uint32_t_pts_to $(base + 8) 1.0R 7ul))
void write_at(void *base) { *(uint32_t *)(base + 8) = 7; }

_ghost_arg(uint32_t x)
_requires(_inline_pulse(uint32_t_pts_to $(base + 4) 1.0R $(x)))
_ensures(_inline_pulse(uint32_t_pts_to $(base + 4) 1.0R $(x)))
_ensures(return == x)
uint32_t read_through(void *base) {
  uint32_t *q = (uint32_t *)(base + 4);
  return *q;
}

_ghost_arg(uint32_t x)
_requires(_inline_pulse(uint32_t_pts_to $(base + 4) 1.0R $(x)))
_ensures(_inline_pulse(uint32_t_pts_to $(base + 4) 1.0R $(x)))
_ensures(return == x)
uint32_t read_bytes_at(_plain uint8_t *base) { return *(uint32_t *)(base + 4); }

// Pointer arithmetic in a contract.
void *advance_spec(void *base) _ensures(return == base + 4) { return base + 4; }

uint32_t *advance_elems(_plain uint32_t *base) _ensures(return == base + 2) {
  return base + 2;
}

void *back_spec(void *base) _ensures(return == base + 4 - 2) {
  void *p = base + 4;
  return p - 2;
}
