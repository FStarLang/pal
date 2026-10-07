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
