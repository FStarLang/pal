/* Test: mutable *array* globals under the bring-your-own-permission model.
 *
 * A mutable array global `T g[N]` emits an assumed handle (`assume val var_g :
 * array T`) and the slprop `_live(g)` stands for, which carries both full
 * ownership of the array and its extent `N`. As with mutable scalar globals,
 * the permission is threaded through contracts by hand and assumed at the
 * entrypoint.
 */

#include "pal.h"
#include <stdint.h>
#include <stddef.h>

uint32_t buf[4];

/* 1.1 `_live(buf)` pins the extent, so a write at the last index verifies with
 * no length precondition of its own. */
void set_last(uint32_t v) _requires(_live(buf)) _ensures(_live(buf))
    _ensures(buf[3] == v) {
  buf[3] = v;
}

/* 1.2 Writing an element, and reading it back in the postcondition. The other
 * cells are named too: the permission hands the whole array back, so a caller
 * that knew something about them keeps knowing it. */
void set(size_t i, uint32_t v) _requires(_live(buf)) _requires(i < 4)
    _ensures(_live(buf)) _ensures(buf[i] == v)
    _ensures(_forall(size_t k, k < 4 && k != i ==> buf[k] == _old(buf[k]))) {
  buf[i] = v;
}

/* 1.3 Reading an element out again. */
uint32_t get(size_t i) _requires(_live(buf)) _requires(i < 4)
    _ensures(_live(buf)) _ensures(return == buf[i]) {
  return buf[i];
}

/* 2.1 Permission threads through a call, like any other resource: the caller
 * holds `_live(buf)`, each callee takes it and hands it back. */
void set_first_two(uint32_t v) _requires(_live(buf)) _ensures(_live(buf))
    _ensures(buf[0] == v) {
  set(1, v);
  set(0, v);
}

/* 2.2 A loop over the array holds the permission across iterations. */
void fill(uint32_t v) _requires(_live(buf)) _ensures(_live(buf))
    _ensures(buf[0] == v) {
  for (size_t i = 0; i < 4; i++)
      _invariant(_live(buf) && _live(i) && i <= 4)
      _invariant(i > 0 ==> buf[0] == v) {
    buf[i] = v;
  }
}

/* 3.1 An array of struct elements works the same way. */
struct point {
  uint32_t px;
  uint32_t py;
};

struct point pts[2];

void set_px(size_t i, uint32_t v) _requires(_live(pts)) _requires(i < 2)
    _ensures(_live(pts)) _ensures(pts[i].px == v) {
  pts[i].px = v;
}

/* 3.2 An array whose extent this translation unit does not know (`extern T g[]`,
 * sized in the defining unit). `_live` then pins no length, so a contract that
 * needs one states it -- as for an `_array T *` parameter. */
extern uint32_t ebuf[];

uint32_t read_ext(size_t i) _requires(_live(ebuf)) _requires(i < ebuf._length)
    _ensures(_live(ebuf)) _preserves_value(ebuf._length)
    _ensures(return == ebuf[i]) {
  return ebuf[i];
}

/* 3.3 The global decays to an array pointer like any C array, and reads through
 * that pointer use the same permission. */
uint32_t first_via_ptr(void) _requires(_live(buf)) _ensures(_live(buf))
    _ensures(return == buf[0]) {
  _array uint32_t *p = buf;
  return p[0];
}

/* 3.4 A two-dimensional global is an `array` of rows. Element reads and
 * writes borrow the row, update it, and hand it back. */
uint32_t grid[3][4];

void grid_set(size_t i, size_t j, uint32_t v) _requires(_live(grid))
    _requires(i < 3 && j < 4) _ensures(_live(grid)) _ensures(grid[i][j] == v) {
  grid[i][j] = v;
}

uint32_t grid_get(size_t i, size_t j) _requires(_live(grid))
    _requires(i < 3 && j < 4) _ensures(_live(grid))
    _ensures(return == grid[i][j]) {
  return grid[i][j];
}

/* 3.5 The same for rows of structs. */
struct point pgrid[2][2];

void pgrid_set_py(size_t i, size_t j, uint32_t v) _requires(_live(pgrid))
    _requires(i < 2 && j < 2) _ensures(_live(pgrid)) {
  pgrid[i][j].py = v;
}

/* 4.1 An entrypoint assumes the permissions for the globals it uses, and gives
 * them back on return. */
int main(void) _requires(_live(buf)) _requires(_live(pts)) _ensures(_live(buf))
    _ensures(_live(pts)) {
  fill(7);
  set_first_two(9);
  set_px(0, 1);
  return get(0) == 9 ? 0 : 1;
}
