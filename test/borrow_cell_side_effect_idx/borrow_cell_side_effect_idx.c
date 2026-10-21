// Regression test for #371: a side-effecting index in `&a[i++]` must be
// evaluated exactly once when borrowing the cell.
#include "pal.h"
#include <stddef.h>
#include <stdint.h>

typedef struct {
  uint64_t start;
  uint64_t end;
} entry;

struct _refine(this.stack._length == this.size && this.count <= this.size) stack {
  _array entry *stack;
  size_t count;
  size_t size;
};

void push_range(struct stack *stk, uint64_t start, uint64_t end)
  _requires(stk->count < stk->size)
  _ensures(stk->count == _old(stk->count) + 1)
{
  entry *me = &stk->stack[stk->count++];
  me->start = start;
  me->end = end;
  _ghost_stmt(array_return_cell $(stk->stack));
}

void set_out(uint64_t *_out p) _ensures(*p == 0) { *p = 0; }

void push_call(_array uint64_t *a, size_t *i, size_t n)
  _requires(a._length == n && *i < n)
  _ensures(*i == _old(*i) + 1)
{
  set_out(&a[(*i)++]);
  _ghost_stmt(array_return_cell $(a));
}
