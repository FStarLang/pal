#include "pal.h"

int test0(int x)
	_ensures(return == 1)
{
  x = 1;
  return x;
}

int test1(int x)
	_ensures(return == 1)
{
  *(&x) = 1;
  return x;
}

int test2(int x)
  _ensures(return == 1)
{
  int *p = &x;
  *p = 1;
  return *p;
}

int test4(int x)
  _ensures(return == 1)
{
  int *p = &x;
  *p = 1;
  return x;
}

int test5(int x)
  _ensures(return == 1)
{
  int *p = &x;
  if (1) {
    *p = 1;
  }
  return x;
}

// TODO in Pulse: Allocating a mutable local variable expects an annotated post-condition
// int test6(int x)
//   _ensures(return == 1)
// {
//   if (1) {
//     int *p = &x;
//     *p = 1;
//   }
//   return x;
// }
