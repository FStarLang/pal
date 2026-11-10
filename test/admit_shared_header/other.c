#include "platform.h"

int platform_identity(int x) {
    __asm__ volatile ("" : "+r"(x));
    return x;
}

int platform_unused(int x) {
    __asm__ volatile ("" : "+r"(x));
    return x;
}
