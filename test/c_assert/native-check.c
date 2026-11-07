#ifndef C2PULSE
#include "pal.h"
#include <assert.h>
#include <stdint.h>

int32_t checked_add(int32_t a, int32_t b);

int main(void) {
    int checks = 0;
    _assert(++checks);
    if (checks != 0)
        return 1;
    assert(++checks);
    if (checks != 1)
        return 2;
    return checked_add(3, 4) != 7;
}
#endif
