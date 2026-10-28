#include "pal.h"
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

// Bitwise and partial operators in contracts.

int32_t not_s(int32_t x) _ensures(return == ~x) { return ~x; }
uint32_t not_u(uint32_t x) _ensures(return == ~x && return + x == 0xFFFFFFFFu) { return ~x; }
int32_t not_s_arith(int32_t x) _ensures(return == -x - 1) { return ~x; }
// The promoted complement, narrowed back.
uint8_t not_u8(uint8_t x) _ensures(return == (uint8_t)~x && return == 255 - x) { return ~x; }
int8_t not_s8(int8_t x) _ensures(return == ~x) { return ~x; }

int32_t and_s(int32_t x, int32_t y) _ensures(return == (x & y)) { return x & y; }
int32_t or_s(int32_t x, int32_t y) _ensures(return == (x | y)) { return x | y; }
int32_t xor_s(int32_t x, int32_t y) _ensures(return == (x ^ y)) { return x ^ y; }
uint32_t and_u(uint32_t x, uint32_t y) _ensures(return == (x & y)) { return x & y; }
uint64_t xor_u(uint64_t x, uint64_t y) _ensures(return == (x ^ y)) { return x ^ y; }

int32_t neg_s(int32_t x) _requires(x > -100) _ensures(return == -x) { return -x; }
uint32_t shl_u(uint32_t x) _requires(x < 32) _ensures(return == (1u << x)) { return 1u << x; }
uint32_t shr_u(uint32_t x) _ensures(return == (x >> 3)) { return x >> 3; }
int32_t shl_s(int32_t x) _requires(x >= 0 && x < 1000) _ensures(return == (x << 2)) { return x << 2; }
int32_t shr_s(int32_t x) _requires(x >= 0) _ensures(return == (x >> 2)) { return x >> 2; }

int32_t div_s(int32_t x, int32_t y) _requires(y > 0) _ensures(return == x / y) { return x / y; }
int32_t mod_s(int32_t x, int32_t y) _requires(y > 0) _ensures(return == x % y) { return x % y; }
uint32_t div_u(uint32_t x, uint32_t y) _requires(y != 0) _ensures(return == x / y) { return x / y; }
uint32_t mod_u(uint32_t x, uint32_t y) _requires(y != 0) _ensures(return == x % y) { return x % y; }

// The flags idiom from issue #349, now with a value claim.
struct dev { int32_t flags; };
#define FLAG_X 4
void clear_x(struct dev *d)
  _preserves(_live(*d))
  _ensures(d->flags == (_old(d->flags) & ~FLAG_X))
{
  d->flags &= ~FLAG_X;
}

uint32_t mask_u(uint32_t x) _ensures(return == (x & 0xff)) { return x & 0xff; }
uint8_t low_bits(uint8_t x) _ensures(return == (uint8_t)(x & ~4)) { return x & ~4; }

int32_t mul_s(int32_t x, int32_t y)
    _requires(x >= -1000 && x <= 1000 && y >= -1000 && y <= 1000)
    _ensures(return == x * y) { return x * y; }

size_t mul_sz(size_t x, size_t y)
    _requires(x <= 1000 && y <= 1000)
    _ensures(return == x * y) { return x * y; }

uint32_t guarded_div_or(uint32_t d)
    _ensures(d == 0 || return / d == 0) { return 0; }

uint32_t guarded_div_negated_and(uint32_t d)
    _ensures(!(d != 0 && return / d != 0)) { return 0; }

uint32_t guarded_div_condition(uint32_t d)
    _ensures((d == 0 || return / d == 0) ? return == 0 : return == 1) {
    return 0;
}

uint32_t guarded_div_and_condition(uint32_t d)
    _ensures((d != 0 && return / d != 0) ? return == 1 : return == 0) {
    return 0;
}

uint32_t guarded_div_branches(uint32_t x, uint32_t y, bool choose_x)
    _requires(choose_x ? x != 0 : y != 0)
    _ensures(return == 0)
    _ensures(return == (choose_x ? return / x : return / y)) {
    return 0;
}

uint32_t call_guarded_div_branches(void) _ensures(return == 0) {
    return guarded_div_branches(0, 1, false) + guarded_div_branches(1, 0, true);
}
