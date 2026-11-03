#include "pal.h"
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

// `write_to` takes a plain `int *` (Pulse `ref`) and writes through it.
void write_to(int *p)
  _ensures(*p == 42)
{
    *p = 42;
}

// `caller` holds a real `_array int *` and wants to hand element `i` to
// `write_to`. Borrowing a cell out of an array always yields a
// `pts_to_maybe_uninit` cell carrying its current optional value; PAL does not
// guess whether that cell is initialized or not, so the adaptation to
// `write_to`'s readable `int *` is applied *by hand*. We borrow the cell into a
// local `ref` (`int *p = &a[i]` emits `array_borrow_cell`), then — since the
// array is fully initialized — reveal the known-initialized cell into a readable
// `pts_to` with `array_cell_read` before the call. To hand it back, we package
// the written cell as a maybe-cell (`intro_maybe_some`) and return it with
// `array_return_cell`.
void caller(_array int *a, size_t i)
  _requires(i < a._length)
{
    int *p = &a[i];
    write_to(p);
}

// `init_cell` takes an `_out int *` — an *uninitialized* `ref`
// (`pts_to_uninit`) that it initializes by writing through.
void init_cell(_out int *p)
  _ensures(*p == 42)
{
    *p = 42;
}

// Handing an array cell to an `_out` parameter. Again PAL only borrows the cell
// as a `pts_to_maybe_uninit`; the user drops its value with `forget_maybe` to
// obtain the uninitialized `ref` (`pts_to_uninit`) that `init_cell` expects.
// Once `init_cell` writes through it, the now-initialized cell is packaged back
// as a maybe-cell (`intro_maybe_some`) and returned with `array_return_cell`.
void caller_out(_array int *a, size_t i)
  _requires(i < a._length)
{
    int *p = &a[i];
    init_cell(p);
}

// Borrow a *genuinely uninitialized* array cell and write through it.
// `_out _array int *a` means PAL requires `a` uninitialized on entry and fully
// initialized on exit. With length 1, the cell at index 0 starts uninitialized;
// borrowing `&a[0]` into a local `ref` hands it out as a maybe-cell, we drop its
// (absent) value with `forget_maybe`, `init_cell` writes 42 through it, and
// returning the cell (packaged as a maybe-cell) leaves the (length-1) array
// fully initialized.
void fill_first(_out _array int *a)
  _requires(a._length == 1)
{
    int *p = &a[0];
    init_cell(p);
}


typedef struct {
  int lo;
  int hi;
} pair;

// Handing a *field* to an `_out` parameter. The field is opened for the
// length of the call exactly as an array element is, and since `p` already
// holds a value the field gives it up before the callee writes through it.
//
// Palow only: PAL models a field of a live struct as something that has to be
// unfolded to raw storage by hand before it can be handed out as a write-only
// `ref`, so the same source needs explicit unfold/fold ghost steps there.
// Palow's field focus is that step, so the call stands on its own.
void init_field(pair *p)
  _requires(_live(*p))
  _ensures(p->hi == 42)
{
    init_cell(&p->hi);
}

// Palow: a local array handed to an `_out _array` parameter. PAL's model has
// no uninitialised-array view, so the whole `_out _array` mode is Palow's.
void fill_two(_out _array int *a)
  _preserves(a._length == 2)
{
  a[0] = 1;
  a[1] = 2;
}

void use_fill_two(void)
{
  int buf[2];
  fill_two(buf);
}

void inspect_array_parameter(int *const *p)
{
}

void fill_addressed_array(_array int *a, bool inspect)
  _requires(a._length == 2)
  _preserves_value(a._length)
{
  if (inspect) {
    inspect_array_parameter(&a);
  }
  fill_two(a);
}

void fill_addressed_output(_out _array int *a, bool inspect)
  _requires(a._length == 2)
  _ensures(_forall(size_t j, j < 2 ==> a[j] == 42))
{
  if (inspect) {
    inspect_array_parameter(&a);
  }
  for (size_t i = 0; i < 2; i++)
    _invariant(i <= 2)
    _invariant(_forall(size_t j, j < i ==> a[j] == 42))
  {
    a[i] = 42;
  }
}

int read_retargeted_array(_array const int *a, _array const int *b, bool replace)
  _requires(a._length == 1 && b._length == 1)
  _ensures(return == (replace ? _old(b[0]) : _old(a[0])))
{
  int result;
  if (replace) {
    a = b;
    result = a[0];
  } else {
    result = a[0];
  }
  return result;
}

// The array behind a struct's `_array` pointer field. Its ownership lives in
// the struct's deep predicate, so handing it to a callee borrows that
// predicate for the length of the statement.
struct holder {
  _array int *cells;
  size_t n;
};

int sum_cells(_array const int *c, size_t n)
  _requires(c._length == n);

int sum_holder(const struct holder *h)
  _requires(h->cells._length == h->n)
{
  return sum_cells(h->cells, h->n);
}
