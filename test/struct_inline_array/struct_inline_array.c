#include "pal.h"

struct mixed {
    _array int *a;
    int b[10];
    int c;
};


int read_first_b(struct mixed *s)
  _ensures(s->b[0] == return)
{
    return s->b[0];
}


int read_third_b(struct mixed *s)
  _ensures(s->b[3] == return)
{
    return s->b[3];
}

int read_first_b_const(const struct mixed *s)
  _ensures(s->b[0] == return)
{
    return s->b[0];
}

void write_first_a0(struct mixed *s, int x)
  _requires(s->a._length >= 1)
  _preserves_value(s->a._length)
  _ensures(s->a[0] == x)
{
    s->a[0] = x;
}


//should this verify?
int read_first_b_by_value(_plain struct mixed s)
 _ensures(s.b[0] == return)
{
    return s.b[0];
}

