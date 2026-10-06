#include "pal.h"
#include <stdbool.h>

struct pt {
  int x;
  int y;
};

struct inner {
  int c;
};

struct outer {
  int a;
  struct inner inner;
  int z;
};

void mk_flat(_out struct pt *p) _ensures(p->x == 1 && p->y == 2) {
  p->x = 1;
  p->y = 2;
}

void mk_nested(_out struct outer *p)
    _ensures(p->a == 4 && p->inner.c == 5 && p->z == 6) {
  p->a = 4;
  p->inner.c = 5;
  p->z = 6;
}

int read_after_write(_out struct pt *p)
    _ensures(p->x == 7 && p->y == 8 && return == 7) {
  p->x = 7;
  int x = p->x;
  p->y = 8;
  return x;
}

void mk_if(_out struct pt *p, bool b) _ensures(p->x == 9 && p->y == 10) {
  if (b) {
    p->x = 9;
    p->y = 10;
  } else {
    p->x = 9;
    p->y = 10;
  }
}

int read_after_if(_out struct pt *p, bool b)
    _ensures(p->x == 11 && p->y == 12 && return == 11) {
  if (b) {
    p->x = 11;
  } else {
    p->x = 11;
  }
  int x = p->x;
  p->y = 12;
  return x;
}

int caller(void) _ensures(return == 3) {
  struct pt p;
  mk_flat(&p);
  return p.x + p.y;
}
