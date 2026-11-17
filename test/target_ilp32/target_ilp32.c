#include "pal.h"
#include <stddef.h>
#include <stdint.h>

/* Translated for a 32-bit target (`compile_flags.txt` selects i386; the
 * freestanding headers are clang's own, so no 32-bit libc is needed). Pointers,
 * `size_t` and `ptrdiff_t` are four bytes wide. */

void *malloc(size_t n);
void free(void *p);

struct node {
  _plain struct node *next;
  uint32_t key;
};

/* Proved for the 32-bit target only; the host build need not agree. */
size_t node_size(void)
  _ensures(return == 8)
{
  return sizeof(struct node) + sizeof(void *) - sizeof(size_t);
}

/* A pointer stored in a struct is read back exactly, and the field after it
 * is at offset four. */
struct node *link(struct node *a, struct node *b)
  _ensures(return == b && a->key == _old(a->key))
{
  a->next = b;
  return a->next;
}

/* `ptrdiff_t` is `int32_t` here. */
ptrdiff_t distance(_array uint32_t *a)
  _requires(a._length == 10)
  _ensures(return == 5)
{
  _arrayptr uint32_t *p = a + 7;
  _arrayptr uint32_t *q = a + 2;
  return p - q;
}

/* A 64-bit value converts to `size_t` modulo 2^32. */
size_t truncate(uint64_t x)
  _ensures(return == _old(x) % 4294967296)
{
  return (size_t)x;
}

/* `malloc` aligns for `max_align_t`, which is enough for a `uint64_t`. */
void alloc_wide(void)
{
  uint64_t *p = malloc(sizeof(uint64_t));
  if (p) {
    *p = 1;
    free(p);
  }
}

/* A `_Bool` converts to the target's pointer-width integers. The difference
 * of two pointers is `ptrdiff_t` itself, so `flag` is converted to it. */
ptrdiff_t bool_to_ptrdiff(_array uint32_t *a, _Bool flag)
  _requires(a._length == 10)
  _ensures(return == (_old(flag) ? 6 : 5))
{
  _arrayptr uint32_t *p = a + 7;
  _arrayptr uint32_t *q = a + 2;
  ptrdiff_t d = (p - q) + flag;
  return d;
}

size_t bool_to_size(_Bool flag)
  _ensures(return == (_old(flag) ? 1 : 0))
{
  size_t n = flag;
  return n;
}

/* A `_Bool` promoted through `uint8_t` and then truth-tested. */
uint32_t bool_via_byte(_Bool flag)
  _ensures(return == (_old(flag) ? 7 : 3))
{
  uint8_t b = flag;
  if (b)
    return 7;
  return 3;
}
