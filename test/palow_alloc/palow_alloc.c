#include "pal.h"
#include <stdlib.h>
#include <stdint.h>

// Allocation. `malloc` is an ordinary function with an ordinary specification
// here, rather than a built-in the emitter pattern-matches on: it hands back
// raw bytes, and the caller claims them at whatever type it likes. The price
// is that the specification is honest about failure, so the resource comes
// back under `unless_null` and the C source has to test the pointer before it
// can touch the storage. The old model's allocator could not fail, so this is
// C that the new model requires and the old one did not.

void alloc_write_free(void)
{
  uint32_t *p = malloc(sizeof(uint32_t));
  if (p == NULL) return;
  *p = 3;
  free(p);
}

// A bare truth test on the pointer, which reaches the IR as `!(_Bool) p` and
// is the same test in the other direction.
//
// The opposite polarity -- `if (p != NULL) { ... }`, where it is the *then* arm
// that owns the block -- is translated too, but cannot be tested here: the old
// model's allocator cannot fail, so it still owns the block on the arm this C
// takes when the pointer is null, and that arm leaks. The emitted shape is in
// `Pulse.Lib.C.Palow.Examples` instead.
void alloc_truth_test(void)
{
  uint32_t *p = malloc(sizeof(uint32_t));
  if (!p) return;
  *p = 1;
  free(p);
}

// `calloc` goes through the same path. Its zeroing is not yet carried into the
// claim, so the block arrives write-only just as `malloc`'s does.
void calloc_write_free(void)
{
  uint32_t *p = calloc(1, sizeof(uint32_t));
  if (p == NULL) return;
  *p = 5;
  free(p);
}

// A block may be read back before it is freed, and an assertion about it goes
// through the same load an assertion about a parameter's pointee does.
void alloc_read_back(void)
{
  uint32_t *p = malloc(sizeof(uint32_t));
  if (p == NULL) return;
  *p = 9;
  _assert(*p == 9);
  free(p);
}

// Allocating a pointer-sized object exercises the same path at the one type
// whose representation is not an integer.
void alloc_pointer(uint32_t *q)
{
  uint32_t **p = malloc(sizeof(uint32_t *));
  if (p == NULL) return;
  *p = q;
  free(p);
}
