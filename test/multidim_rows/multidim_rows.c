/* Test: indexing a multidimensional array that is live memory.
 *
 * `a[i]` of a `T a[M][N]` is a ROW: the N elements at `a + i*N`. PAL models
 * `T a[M][N]` as `array (full_array_lspec T N)`, so a live row is borrowed
 * out of its parent's mask (`array_borrow_row`) and must be given back. A
 * complete write `a[i][j] = v` returns the rows it borrowed at once, so a
 * second write to the same row can borrow it again. A read by value needs no
 * borrow at all, and so works at a fractional permission.
 */

#include "pal.h"
#include <stdint.h>
#include <stddef.h>

struct twodim {
  uint32_t arr[3][4];
};

void set_cell(struct twodim *m, size_t i, size_t j, uint32_t v)
    _requires(i < 3 && j < 4) {
  m->arr[i][j] = v;
}

/* Two writes to the same row: the first must hand its row back. */
void set_row_pair(struct twodim *m, size_t i) _requires(i < 3) {
  m->arr[i][0] = 5;
  m->arr[i][1] = 6;
}

/* By-value read through a const pointer. */
uint32_t get_cell(const struct twodim *m) { return m->arr[2][3]; }

/* Rows of structs: a field write through two subscripts. */
struct slot {
  uint64_t pool;
  uint64_t cnt;
};

struct slots {
  struct slot s[2][2];
};

void set_pools(struct slots *a, size_t g, uint64_t x, uint64_t y)
    _requires(g < 2) {
  a->s[g][0].pool = x;
  a->s[g][1].pool = y;
}
