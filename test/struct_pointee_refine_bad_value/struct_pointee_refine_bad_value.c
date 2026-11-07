#include "pal.h"

struct _refine(_inline_pulse(pure (FStar.Int32.v $(this.x) > 0))) positive {
  int x;
};

void bad_output(_out struct positive *p) {
  p->x = 0;
}
