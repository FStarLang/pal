#include "pal.h"
#include <stdbool.h>

void label_old_param_ok(_out int *Out, int n, bool first)
  _ensures(*Out == n)
{
  if (first) {
    *Out = n;
    goto Finally;
  }
  if (n == 0) {
    *Out = n;
    goto Finally;
  }
  *Out = n;
Finally: _ensures(_live(Out) && _live(*Out) && _live(n) && _live(first) && *Out == n && n == _old(n) && Out == _old(Out))
  return;
}

int loop_old_param(int n)
  _ensures(return == n)
{
  int i = 0;
  while (i < 2)
    _invariant(_live(i))
    _invariant(_live(n))
    _invariant(n == _old(n))
  {
    i++;
  }
  return n;
}

void label_old_param_missing(_out int *Out, int n, bool first)
  _ensures(*Out == n)
{
  if (first) {
    *Out = n;
    goto Finally;
  }
  if (n == 0) {
    *Out = n;
    goto Finally;
  }
  *Out = n;
Finally: _ensures(_live(Out) && _live(*Out) && _live(n) && _live(first) && *Out == n)
  return;
}
