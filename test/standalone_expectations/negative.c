#include "pal.h"
#undef assert

void negative(void) {
    _ghost_stmt(assert (pure False));
}
