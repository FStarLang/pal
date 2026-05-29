#include "pal.h"
#include <stdbool.h>

bool is_eq(int a1, int a2)
  _ensures(return == (a1 == a2))
{
  if (a2 <= a1) {
    return a1 == a2;
  } else {
    return false;
  }
}