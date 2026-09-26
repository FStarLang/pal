#include "pal.h"

typedef struct int_pair {
  int a;
  int b;
} int_pair;

void swap_inplace(int_pair *x)
  _ensures(x->a == _old(x->b))
  _ensures(x->b == _old(x->a))
{
  int tmp = x->a;
  x->a = x->b;
  x->b = tmp;
}

int_pair swap_functional(int_pair x)
  _ensures(return.a == x.b && return.b == x.a)
{
  swap_inplace(&x);
  return x;
}

void use_swap() {
  int_pair x = { .a = 1, .b = 2 };
  swap_inplace(&x);
#ifdef PALOW
  // Palow spells a structure's ownership with the predicate generated for
  // that structure, at an explicit permission; there is no overloaded
  // `pts_to`.
  _assert(_inline_pulse(struct_int_pair_pts_to $(&x) 1.0R
                          $((int_pair) { .a = 2, .b = 1 })));
#else
  _assert(_inline_pulse(pts_to $(&x) $((int_pair) { .a = 2, .b = 1 })));
#endif
}
