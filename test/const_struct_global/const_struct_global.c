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

/* A table whose element has an array field: such a struct has no `_repr`, so
   no array fill may be generated for it -- while another function still
   needs one, for a local array with a constant initialiser. */
struct named {
  char name[4];
  int v;
};

static const struct named named_table[] = { { "ab", 1 }, { "cd", 2 } };

char first_of_local(void)
  _ensures(return == 'o')
{
  char buf[3] = "ok";
  return buf[0];
}

/* An opaque table: a function pointer's entry unfolds to its callee's whole
   contract, so the value is kept from the solver until a proof reveals it.
   A read of a field is still folded to the initialiser's constant; what the
   attribute hides is the value as a specification names it. */
static const _pulse_opaque_to_smt struct ops opaque_ops = { .f = inc, .k = 4 };

int use_opaque_k(void)
  _ensures(return == 4)
{
  return opaque_ops.k;
}

void reveal_opaque_ops(void)
  _ensures(_inline_pulse(pure (Global_opaque_ops.var_opaque_ops.Struct_ops.fld_k == 4l)))
{
  _ghost_stmt(Opaque_ops.k_is_four ());
}
