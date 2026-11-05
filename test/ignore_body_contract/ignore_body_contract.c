#include "pal.h"
#include <stdint.h>

_pal_ignore_body
int bad_contract(int x) _requires(unknown_contract_variable) {
    __asm__ volatile ("");
    return x;
}
