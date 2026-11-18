#include "pal.h"
#include <stdint.h>

int admitted_here(int x) _ensures(return == x) { return x; }

_pal_admit int admitted_there(int x) _ensures(return == x) {
    __asm__ volatile ("" : "+r"(x));
    return x;
}

int ignored_here(int x) { return x; }
