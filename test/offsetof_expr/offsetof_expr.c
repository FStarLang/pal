#include "pal.h"
#include <stdint.h>
#include <stddef.h>

struct S { uint64_t a; uint64_t b; };
struct T { uint8_t tag; struct S s; uint32_t arr[4]; };

size_t off_b(void) _ensures(return == 8) { return offsetof(struct S, b); }

size_t off_nested(void) _ensures(return == 16) { return offsetof(struct T, s.b); }

size_t off_arr(void) _ensures(return == 28) { return offsetof(struct T, arr[1]); }

size_t desc_table(void) _ensures(return == 8) {
  size_t offs[2] = { offsetof(struct S, a), offsetof(struct S, b) };
  return offs[0] + offs[1];
}
