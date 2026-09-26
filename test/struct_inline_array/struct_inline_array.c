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


int read_first_b_by_value(_plain struct mixed s)
 _ensures(s.b[0] == return)
{
    return s.b[0];
}


struct containsarray {
    int b[10];
};

void write_fifth_b(struct containsarray *a, int v)
  _ensures(a->b[5] == v)
{
    a->b[5] = v;
}

int read_from_initializer(unsigned i)
    _requires(i < 10)
    _ensures(return == i)
{
    _pure struct containsarray a = {
        .b = { 0,1,2,3,4,5,6,7,8,9 }
    };
    return a.b[i];
}

_pure struct containsarray global;
int read_global(unsigned i)
    _requires(i < 10)
    _ensures(return == 0)
{
    return global.b[i];
}

_pure struct containsarray data = {
    .b = { 0,1,2,3,4,5,6,7,8,9 }
};
int read_data(unsigned i)
    _requires(i < 10)
    _ensures(return == i)
{
    return data.b[i];
}

_pure int global_array[10] = { 0,1,2,3,4,5,6,7,8,9 };
int read_global_array(unsigned i)
    _requires(i < 10)
    _ensures(return == i)
{
    return global_array[i];
}

struct twodim {
    int arr[3][4];
};

int access(const struct twodim *m) {
    return m->arr[2][3];
}

// A write through a multidimensional field, and a contract that names the
// element it changed. C lays `int arr[3][4]` out as twelve consecutive ints,
// so `arr[1][2]` is the sixth of them and the outer subscript is an offset
// rather than a separate object.
//
// Palow-only: PAL's array model gives the outer subscript its own `array`
// handle, and the inner write is then applied to a `full_array_lspec` rather
// than to an array (Error 189). The flat view has no such intermediate to get
// wrong, which is the point of stating it flat.
#ifdef PALOW
void set_cell(struct twodim *m, int v)
  _ensures(m->arr[1][2] == v)
{
    m->arr[1][2] = v;
}
#endif
// A scalar field of a structure passed by value. There is no storage to read
// from: the parameter is the record, so the access is a projection.
int read_c_by_value(_plain struct mixed s)
 _ensures(s.c == return)
{
    return s.c;
}
