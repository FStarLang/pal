#include "pal.h"

typedef struct {
  int a;
  int b;
} int_pair;

int_pair swap_functional(int_pair x)
  _ensures(return.a == x.b && return.b == x.a)
{
  int_pair result = (int_pair) { .a = x.b, .b = x.a };
  return result;
}