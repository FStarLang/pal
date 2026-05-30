#include "pal.h"

typedef struct {
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
