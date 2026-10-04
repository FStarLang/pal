/* Test: borrowing a cell of a stack-local array as a pointer.
 *
 * `T *p = &a[i];` over a fixed-size local array lowers to the same
 * `array_borrow_cell` as over an `_array` parameter: the local holds the
 * array, the cell is handed out as a `ref`, and it must be given back with
 * `array_return_cell` / `array_return_cell_unchanged` before the array is
 * used whole again (or freed at the end of its scope). The arrays are
 * initialized first with a whole-array memset, since `fill` updates in place.
 */

#include "pal.h"
#include <stdint.h>
#include <stddef.h>
#include <string.h>

#define N 4

typedef struct Desc {
  uint64_t Start;
  uint32_t Count;
  uint32_t Index;
} Desc;

/* Updates the cells in place, so they must already hold values. */
void fill(_array Desc *out, uint16_t n) _requires(out._length == n)
    _ensures(out._length == n);
uint32_t use(uint64_t start, uint32_t count);

/* Read-only walk over a batch loaded into a stack array. */
uint32_t walk(uint16_t n)
  _requires(n <= N)
{
  Desc local[N];
  uint32_t total = 0;
  memset(local, 0xFF, sizeof(local));
  fill(local, N);
  for (uint16_t i = 0; i < n; i++)
    _invariant(_live(i) && _live(total) && i <= n && n <= N)
    _invariant(local._length == N)
  {
    Desc const *d = &local[i];
    total = use(d->Start, d->Count);
    _ghost_stmt(Pulse.Lib.C.Array.array_return_cell_unchanged (!var_local));
  }
  return total;
}

/* Writing through the borrowed cell is observed once the cell is returned. */
uint32_t write_cell(void)
  _ensures(return == 7)
{
  Desc local[N];
  memset(local, 0, sizeof(local));
  fill(local, N);
  Desc *d = &local[2];
  d->Count = 7;
  _ghost_stmt(Pulse.Lib.C.Array.array_return_cell (!var_local));
  return local[2].Count;
}

/* Negative: the index must be in bounds. */
uint32_t cell_out_of_bounds(uint16_t n)
  _requires(n <= N)
{
  Desc local[N];
  memset(local, 0, sizeof(local));
  fill(local, N);
  Desc const *d = &local[n];
  uint32_t r = d->Count;
  _ghost_stmt(Pulse.Lib.C.Array.array_return_cell_unchanged (!var_local));
  return r;
}

/* Negative: the array cannot be used whole while a cell is borrowed. */
void cell_not_returned(void)
{
  Desc local[N];
  memset(local, 0, sizeof(local));
  fill(local, N);
  Desc *d = &local[1];
  d->Count = 1;
  fill(local, N);
}
