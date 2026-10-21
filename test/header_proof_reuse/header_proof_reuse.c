#include "pal.h"
#include <stdint.h>

#define UNIT_VALUE 1
#include "helpers.h"

int32_t use_a(void) _ensures(return == 3) {
    shared_zero();
    shared_not(false);
    variant_body();
    variant_contract(1);
    private_read();
    int32_t (*fp)(void) = addressed;
    return shared_increment(2);
}

int32_t read_a(int32_t *p) _ensures(return == *p) {
    return shared_read(p);
}

int32_t ghost_a(_plain int32_t *p)
    _preserves(_inline_pulse(Pulse.Lib.Reference.pts_to $(p) #1.0R 3l))
    _ensures(return == 3)
{
    return shared_ghost(p);
}

int32_t false_a(void) _ensures(return == 4) {
    return shared_increment(2);
}
