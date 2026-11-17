#include "pal.h"
#include <stdint.h>

int platform_identity(int x) _ensures(return == x);

_pal_ignore
int platform_identity(int x) {
    __asm__ volatile ("" : "+r"(x));
    return x;
}
