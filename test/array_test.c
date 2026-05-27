#include "pal.h"
#include <stdlib.h>

void foo(unsigned a[])
  _requires(a._length == 2)
  _preserves_value(a._length)
  _ensures(a[0] == 42)
{
  a[0] = 42;
  a[1] = a[0] + 67;
}

void ptr_attr(_array unsigned *a)
  _requires(a._length == 2)
  _preserves_value(a._length)
  _ensures(a[0] == 42)
{
  a[0] = 42;
  a[1] = a[0] + 67;
}

typedef unsigned *uptr _array;
void tydef_array(uptr a)
  _requires(a._length == 2)
  _preserves_value(a._length)
  _ensures(a[0] == 42)
{
  a[0] = 42;
  a[1] = a[0] + 67;
}

typedef struct {
  _array unsigned *x;
} uptr_struct;
void struct_arr(uptr_struct a)
  _requires(a.x._length == 2)
  _preserves_value(a.x._length)
  _ensures(a.x[0] == 42)
{
  a.x[0] = 42;
  a.x[1] = a.x[0] + 67;
}

_refine(this.x._length == 32)
typedef struct {
  _array unsigned char *x;
} b32_struct;
void b32_arr(b32_struct a)
  _ensures(a.x[10] == 67)
{
  a.x[10] = 67;
}

typedef struct {
  _array int *x, *y;
} two_arrays;
void test_two_arrays() {
  two_arrays p = {
    .x = (int *)calloc(3, sizeof(int)),
    .y = (int *)malloc(4 * sizeof(int))
  };
  p.x[2] = 3;
  free(p.x);
  free(p.y);
}