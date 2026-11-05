#include "pal.h"
#include <stdint.h>

_pal_ignore
long double omitted(long double x) _requires(not_a_contract) {
    __asm__ volatile ("");
    return x;
}

_pal_ignore _pal_admit
long double omitted_both(long double x) _ensures(not_a_contract) {
    __asm__ volatile ("");
    return x;
}

_pal_ignore
long double omitted_forward(long double x) _requires(not_a_contract);

long double omitted_forward(long double x) {
    __asm__ volatile ("");
    return x;
}

int identity(int x) _pal_admit _ensures(return == x) {
    struct unsupported_body_type { int signed_bitfield : 3; };
    __asm__ volatile ("" : "+r"(x));
    return x;
}

_pal_admit
int inherited_identity(int x) _ensures(return == x);

int inherited_identity(int x) {
    __asm__ volatile ("" : "+r"(x));
    return x;
}

int use_identity(int x) _ensures(return == x) {
    return identity(x);
}

int use_inherited_identity(int x) _ensures(return == x) {
    return inherited_identity(x);
}

_pal_admit
static inline int inline_identity(int x) _ensures(return == x) {
    __asm__ volatile ("" : "+r"(x));
    return x;
}

int use_inline_identity(int x) _ensures(return == x) {
    return inline_identity(x);
}
