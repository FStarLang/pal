#include "pal.h"
#include <stdint.h>

struct baz {
    struct {
        int x;
    } foo, bar;
};

int frob(struct baz *b)
    _ensures(b->foo.x == b->bar.x)
    _ensures(return == b->foo.x)
{
    b->bar.x = b->foo.x;
    return b->bar.x;
}

typedef struct profile profile;
typedef struct profiles profiles;

struct profile {
  const char *name;
};

struct profiles {
  profile vivify1;
  struct {
    profile **begin, **end, **allocated;
  } stack;
};
