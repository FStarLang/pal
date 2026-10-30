#include "pal.h"
#include <stdint.h>

struct _refine(_inline_pulse(pure (FStar.Int32.v $(this.x) > 0))) positive {
  int x;
};

struct box {
  struct positive value;
};

struct outer {
  struct box inner;
};

void bad_nested_output(_out struct outer *p) {
  p->inner.value.x = 0;
}
