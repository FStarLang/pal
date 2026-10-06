#include "pal.h"

struct inner {
  int z;
};

struct ops {
  int (*f)(int);
  int (*g)(int);
  struct inner nested;
  int k;
};

int inc(int x)
  _requires(x < 100)
  _ensures(return == x + 1)
{
  return x + 1;
}

static const struct ops my_ops = { .f = inc, .nested = { .z = 7 }, .k = 3 };

int use_k(void)
  _ensures(return == 3)
{
  return my_ops.k;
}

int use_nested(void)
  _ensures(return == 7)
{
  return my_ops.nested.z;
}

int use_default_null(void)
  _ensures(return == 1)
{
  return my_ops.g == 0;
}

int call_f(void)
  _ensures(return == 9)
{
  return my_ops.f(8);
}
