#include "pal.h"
#include <stdint.h>

// Typedefs that are more than a new spelling of their type.
int aligned_local(int x)
{
  typedef int __attribute__((aligned(16))) aint;
  aint y = x;
  return y;
}

int refined_local(int x)
  _requires(x > 0)
{
  typedef _refine(this > 0) int pos;
  pos y = x;
  return y;
}

int vla_local(int n, int x)
  _requires(n > 0)
{
  typedef int row[n];
  return x;
}
