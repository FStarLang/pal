#include "pal.h"
#include <stdint.h>
#include <stdbool.h>

extern uint32_t zero_result(uint32_t d)
    _ensures(d == 0 || return / d == 0);

void cannot_assume_nonzero(void) _ensures(false) {
    zero_result(0);
}
