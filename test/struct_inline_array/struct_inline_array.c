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

// this fails because pulse wrongly unifies the evar in the post
// void write_first_b0(struct mixed *s, int x)
//   _ensures(s->b[0] == x)
// {
//     s->b[0] = x;
// }

// should this verify?
// int read_first_b_by_value(_plain struct mixed s)
//  _ensures(s.b[0] == return)
// {
//     return s.b[0];
// }