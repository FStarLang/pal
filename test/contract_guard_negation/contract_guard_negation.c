#include "pal.h"
#include <stdint.h>

void needs_defined(uint32_t d)
    _requires(!(d != 0 && d / (d - 1u) == 0)) {
}

void cannot_hide_undefined(void) {
    needs_defined(1);
}
